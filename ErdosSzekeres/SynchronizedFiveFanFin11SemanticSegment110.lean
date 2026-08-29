module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment109

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 110. -/

theorem synchronizedFiveFanFin11Semantic_clause07904 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1152 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1030 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1152 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07905 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1471 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1591 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1471 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1591 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07906 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1153 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1031 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0543
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07907 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1153 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1031 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0543
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07908 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1153 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1031 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0543
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07909 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1153 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1031 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0543
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07910 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1472 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1592 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1396 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1472 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1592 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0543
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07911 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0959 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0980 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1154 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0959 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0980 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1032 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1154 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1055
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07912 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0959 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0980 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1154 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0959 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0980 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1032 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1154 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1055
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07913 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1474 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1594 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1474 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1594 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 6}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0111
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07914 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0960 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0981 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1155 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0981 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1033 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1155 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 6}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0111
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07915 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1474 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1594 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1474 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1594 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 6}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0111
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07916 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0960 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0981 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1155 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0981 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1033 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1155 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 6}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0111
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07917 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1474 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1594 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1474 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1594 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 6}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0111
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07918 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1388 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1399 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1420 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1475 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1595 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1388 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1399 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1420 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1475 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1595 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 7}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0175
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07919 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0950 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0961 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0982 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1156 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0950 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0961 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0982 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1034 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1156 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 7}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0175
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07920 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1596 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1476 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1596 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07921 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0983 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1157 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0983 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1035 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1157 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07922 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1596 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1476 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1596 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07923 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0983 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1157 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0983 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1035 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1157 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07924 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1596 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1476 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1596 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07925 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0983 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1157 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0983 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1035 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1157 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07926 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1596 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1476 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1596 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 8}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0303
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07927 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1422 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1477 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1597 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1422 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1477 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1597 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0559
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07928 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1158 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1036 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1158 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0559
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07929 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1422 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1477 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1597 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1422 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1477 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1597 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 9}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0559
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07930 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1158 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1036 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1158 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0559
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07931 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1158 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1036 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1158 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0559
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07932 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1478 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1598 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1478 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1598 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1071
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07933 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1478 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1598 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1478 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1598 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1071
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07934 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1478 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1598 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1478 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1598 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1071
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07935 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1388 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1403 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1424 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1479 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1599 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1388 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1403 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1424 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1479 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1599 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 7}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0207
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07936 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1480 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1600 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1480 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1600 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 8}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0335
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07937 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1161 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1161 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 8}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0335
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07938 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1161 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1161 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 8}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0335
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07939 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1480 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1600 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1480 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1600 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0335
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07940 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1161 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1161 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 8}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0335
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07941 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1480 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1600 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1480 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1600 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 8}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0335
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07942 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1481 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1601 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1481 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1601 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0591
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07943 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1162 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0591
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07944 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1162 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0591
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07945 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1162 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0591
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07946 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1481 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1601 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1481 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1601 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0591
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07947 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1482 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1602 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1482 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1602 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1103
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07948 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0968 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0989 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1163 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0968 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0989 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1041 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1163 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1103
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07949 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1482 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1602 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1482 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1602 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 10}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1103
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07950 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1482 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1602 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1482 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1602 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 6, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1103
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07951 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1388 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1407 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1428 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1483 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1603 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1388 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1407 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1428 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1483 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1603 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0399
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07952 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1486 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1606 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1486 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1606 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0783
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07953 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0993 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1166 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0993 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1166 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0783
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07954 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0993 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1166 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0993 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1166 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0783
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07955 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1486 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1606 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1486 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1606 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0783
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07956 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0993 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1166 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0993 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1166 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0783
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07957 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1487 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1607 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1487 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1607 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1295
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07958 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1487 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1607 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1487 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1607 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1295
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07959 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1488 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1608 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1488 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1608 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1551
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07960 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1168 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0995 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1047 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1168 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1551
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07961 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1168 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0995 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1047 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1168 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1551
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07962 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1168 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0995 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1047 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1168 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1551
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07963 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0960 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1169 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1169 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 6}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0119
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07964 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1489 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1609 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1489 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1609 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 6}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0119
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07965 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0960 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1169 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1169 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 6}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0119
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07966 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1489 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1609 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1489 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1609 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 6}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0119
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07967 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0956 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0961 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0997 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1170 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0956 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0961 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0997 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1049 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1170 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 7}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0183
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07968 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0998 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1171 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0998 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1050 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1171 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 8}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0311
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07969 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1491 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1611 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1491 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1611 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 8}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0311
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

theorem synchronizedFiveFanFin11Semantic_clause07970 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1491 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1611 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1491 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1611 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0311
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

theorem synchronizedFiveFanFin11Semantic_clause07971 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1491 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1611 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1491 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1611 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 8}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0311
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

theorem synchronizedFiveFanFin11Semantic_clause07972 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1492 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1612 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1396 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1492 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1612 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 9}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0567
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07973 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1172 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1051 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1172 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0567
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07974 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1492 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1612 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1396 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1492 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1612 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 5, 9}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0567
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
