module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment111

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 112. -/

theorem synchronizedFiveFanFin11Semantic_clause08046 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1631 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1511 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0807
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08047 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1191 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1017 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1070 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1191 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0807
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08048 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1512 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1319
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08049 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1512 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1319
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08050 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0964 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0973 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1192 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0964 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0973 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1018 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1071 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1192 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1319
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

theorem synchronizedFiveFanFin11Semantic_clause08051 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1632 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1512 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 8, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1319
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08052 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1513 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08053 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0964 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0964 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1019 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1072 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 4, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08054 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1513 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08055 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0964 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0964 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1019 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1072 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08056 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1633 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1513 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08057 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0964 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1193 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0964 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1019 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1072 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08058 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1403 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1408 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1515 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1635 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1403 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1408 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1515 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 7, 9}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0711
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08059 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0965 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0970 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1195 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0965 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0970 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1021 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1074 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 7, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0711
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08060 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1403 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1409 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1403 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1409 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1461 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1516 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 7, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1223
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08061 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1403 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1409 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1636 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1403 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1409 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1461 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1516 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 7, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1223
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08062 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0965 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0968 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0971 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1196 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0104 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0965 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0968 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0971 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1022 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1075 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1196 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 7, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1223
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08063 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1517 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0839
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08064 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1517 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0839
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08065 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1076 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0839
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08066 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1637 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1517 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0839
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08067 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1518 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1351
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08068 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1518 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1351
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08069 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0968 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0973 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1198 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0968 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0973 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1024 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1077 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1351
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08070 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1518 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 10}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1351
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08071 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1518 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1351
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08072 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1607
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08073 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1607
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08074 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0968 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0968 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1607
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08075 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0968 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0968 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1607
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08076 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1523 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 8, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1799
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08077 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1523 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1799
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08078 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0973 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0973 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1026 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1082 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 8, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1799
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08079 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0973 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1201 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0973 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1026 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1082 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1799
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08080 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1642 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1523 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1642 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 8, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1799
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08081 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0981 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1202 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0981 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1083 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1202 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 6}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0123
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08082 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1643 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1524 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1643 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 6}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0123
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08083 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0981 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1202 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0981 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1083 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1202 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 6}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0123
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08084 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1643 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1524 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1643 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 6}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0123
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08085 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1643 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1524 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1643 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 6}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0123
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08086 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0977 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0982 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0997 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1203 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0977 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0982 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0997 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1084 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1203 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 7}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0187
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08087 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1645 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1526 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1645 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 8}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0315
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08088 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0983 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0998 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1204 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0983 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0998 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1085 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1204 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 8}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0315
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08089 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1645 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1526 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1645 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0315
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08090 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1645 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1526 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1645 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 8}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0315
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08091 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1205 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1086 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1205 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 9}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0571
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08092 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1422 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1646 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1422 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1527 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1646 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0571
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08093 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1205 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1086 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1205 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0571
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08094 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1205 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1086 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1205 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0571
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08095 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1205 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1086 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1205 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0571
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08096 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0980 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0985 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1206 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0980 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0985 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1087 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1206 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1083
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08097 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1418 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1647 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1418 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1528 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1647 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 10}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1083
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08098 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0980 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0985 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1206 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0980 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0985 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1087 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1206 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1083
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08099 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1418 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1647 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1418 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1528 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1647 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 5, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1083
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08100 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1415 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1424 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1648 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1415 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1424 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1529 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1648 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 7}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0219
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08101 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0977 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0986 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1207 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0977 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0986 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1001 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1088 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1207 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 7}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0219
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08102 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0977 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0986 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1207 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0977 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0986 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1001 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1088 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1207 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 7}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0219
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08103 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1649 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1530 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1649 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 8}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0347
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

theorem synchronizedFiveFanFin11Semantic_clause08104 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1208 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1002 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1089 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1208 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 8}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0347
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08105 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1208 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1002 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1089 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1208 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 8}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0347
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08106 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1649 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1530 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1649 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0347
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

theorem synchronizedFiveFanFin11Semantic_clause08107 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1208 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1002 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1089 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1208 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 8}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0347
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08108 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1649 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1530 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1649 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 8}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0347
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

theorem synchronizedFiveFanFin11Semantic_clause08109 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08110 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1650 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1531 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1650 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08111 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08112 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 7, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08113 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08114 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1650 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1531 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1650 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08115 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1209 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1209 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08116 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1650 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1531 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1650 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0603
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
