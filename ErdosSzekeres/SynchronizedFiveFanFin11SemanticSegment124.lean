module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment123

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 124. -/

theorem synchronizedFiveFanFin11Semantic_clause08898 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1657 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1669 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1795 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1657 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1669 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1795 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 7, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1258
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08899 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08900 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08901 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08902 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1218 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1219 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1224 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1229 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1258 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1355 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1218 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1219 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1224 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1229 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1258 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08903 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1386
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08904 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1386
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08905 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1797 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1386
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08906 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1642
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08907 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1219 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1220 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1226 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1219 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1220 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1226 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1642
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08908 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1642
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08909 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1798 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1642
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08910 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1219 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1220 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1226 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1357 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1219 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1220 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1226 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1642
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08911 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1799 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1661 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1662 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1673 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1702 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1799 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0938
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08912 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1799 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1661 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1662 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1673 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1702 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1799 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0938
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08913 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1221 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1222 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1224 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1232 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1261 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1358 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1221 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1222 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1224 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1232 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1261 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1358 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0938
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08914 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1800 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1661 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1674 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1703 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1800 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1450
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08915 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1800 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1661 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1674 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1703 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1800 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1450
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08916 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1800 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1661 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1674 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1703 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1800 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1450
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08917 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1801 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1662 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1675 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1801 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1706
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08918 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1801 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1662 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1675 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1801 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1706
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08919 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1801 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1662 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1675 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1801 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1706
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08920 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1834
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

theorem synchronizedFiveFanFin11Semantic_clause08921 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1834
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

theorem synchronizedFiveFanFin11Semantic_clause08922 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1834
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

theorem synchronizedFiveFanFin11Semantic_clause08923 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1224 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1225 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1226 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1235 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1264 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1361 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1224 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1225 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1226 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1235 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1264 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1834
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08924 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1802 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1834
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

theorem synchronizedFiveFanFin11Semantic_clause08925 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1668 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1669 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1804 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1668 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1669 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1675 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1804 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1738
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08926 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1227 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1228 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1234 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1265 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1363 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1227 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1228 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1234 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1265 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1363 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1738
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08927 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1866
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08928 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1229 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1230 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1235 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1364 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1229 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1230 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1235 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 8, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1866
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08929 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1866
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08930 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1805 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1866
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08931 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1806 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1677 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1681 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1687 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1696 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1806 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 7, 8}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0498
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08932 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1697 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1807 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1677 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1688 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1697 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1807 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0754
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08933 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1236 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1241 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1247 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1256 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1367 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1236 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1247 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1256 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1367 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0754
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08934 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1808 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1677 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 7, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1266
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08935 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1808 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1677 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 7, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1266
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08936 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1237 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1243 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1258 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1369 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1237 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1243 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1258 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0882
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08937 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1690 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1809 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1690 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1809 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0882
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08938 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1237 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1244 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1259 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1237 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1244 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1259 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 8, 10}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1394
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08939 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1810 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1810 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1394
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08940 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08941 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08942 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08943 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08944 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08945 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08946 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1811 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1650
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08947 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1240 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1242 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1244 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1252 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1262 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1373 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1240 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1242 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1244 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1252 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1262 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1373 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 8, 10}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1458
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08948 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1812 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1681 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1693 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1703 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1812 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 8, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1458
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08949 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1812 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1681 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1693 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1703 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1812 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1458
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08950 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1813 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1813 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1714
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08951 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1241 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1242 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1263 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1242 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1263 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1714
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08952 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1241 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1242 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1263 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1242 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1263 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1714
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08953 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1813 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1813 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1714
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08954 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1241 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1242 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1263 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1374 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1242 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1263 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1714
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08955 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1813 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1813 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 7, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1714
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08956 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1243 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1244 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1264 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1243 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1244 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1264 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1842
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08957 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1814 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1814 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1842
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08958 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1814 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1814 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 8, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1842
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08959 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1243 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1244 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1264 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1375 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1243 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1244 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1264 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1842
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08960 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1814 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1814 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 8, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1842
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08961 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1815 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1687 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1693 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1707 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1815 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 7, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1490
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08962 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1247 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1248 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1265 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1247 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1248 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1265 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 7, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1746
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08963 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1816 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1688 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1816 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 7, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1746
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08964 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1816 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1688 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1816 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 7, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1746
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08965 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1247 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1248 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1265 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1378 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1247 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1248 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1265 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1746
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08966 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 8, 9, 10}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08967 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1379 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 8, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08968 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
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
      ¬SynchronizedFiveFanFin11SemanticAtom1690 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1817 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h4
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
  unfold SynchronizedFiveFanFin11SemanticAtom1690 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1817 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 6, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 6, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 6, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
