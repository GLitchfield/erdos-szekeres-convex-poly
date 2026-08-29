module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment113

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 114. -/

theorem synchronizedFiveFanFin11Semantic_clause08188 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1552 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1355
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08189 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1671 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1552 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1355
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08190 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1611
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08191 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1611
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08192 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0989 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0989 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0995 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1112 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1611
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08193 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0989 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0989 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0995 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1112 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1611
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08194 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1611
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08195 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1556 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1803
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08196 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1556 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 8, 9, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1803
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08197 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1676 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1556 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 8, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1803
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08198 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1558 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 8}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0371
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08199 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1558 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 8}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0371
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08200 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1558 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 8}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0371
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08201 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1678 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1558 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 8}, 10, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0371
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08202 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1118 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 9}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0627
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08203 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1559 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0627
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08204 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1118 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 9}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0627
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08205 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1679 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1559 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 9}, 8, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0627
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08206 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1004 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1013 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1119 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1139
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08207 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1560 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1139
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08208 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1560 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 10}, 8, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1139
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08209 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1680 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1560 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1139
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08210 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1435 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1444 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1562 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1682 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1435 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1444 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1454 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1562 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 7, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0691
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08211 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0997 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1241 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0997 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1006 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1015 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1121 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 7, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0691
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08212 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0997 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1241 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0997 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1006 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1015 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1121 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0691
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08213 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1435 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1445 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1455 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1435 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1445 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1455 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1563 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 7, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1203
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08214 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1435 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1445 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1455 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1683 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1435 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1445 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1455 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1563 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 7, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1203
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08215 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1684 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1564 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0819
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08216 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0998 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1243 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0998 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1007 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1017 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1123 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1243 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0819
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08217 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1684 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1564 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0819
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08218 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0998 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1244 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0998 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1008 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1018 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1124 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1244 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 8, 10}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1331
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08219 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1447 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1685 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1447 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1565 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 8, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1331
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08220 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1019 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1125 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1587
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08221 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1566 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1587
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08222 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1566 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1587
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08223 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1245 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1019 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1125 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1587
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08224 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1686 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1566 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 9, 10}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1587
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08225 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1443 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1687 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1443 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1459 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1567 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1687 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 7, 8}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0467
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08226 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1443 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1687 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1443 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1459 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1567 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1687 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 7, 8}, 10, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0467
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08227 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1444 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1568 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1688 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1444 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1568 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1688 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0723
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08228 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1445 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1445 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1461 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1569 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 7, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1235
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08229 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1690 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1570 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1690 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0851
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08230 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1249 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1002 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1007 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1129 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at h20
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0851
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

theorem synchronizedFiveFanFin11Semantic_clause08231 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1447 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1691 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1447 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1571 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 8, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1363
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08232 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1447 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1691 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1447 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1571 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1363
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08233 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1004 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1619
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08234 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1572 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1572 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1619
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08235 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1004 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1619
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08236 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1004 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1619
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08237 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1572 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1572 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 6, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1619
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08238 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1444 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1445 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1466 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1694 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1444 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1445 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1466 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1574 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 7, 9, 10}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1683
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08239 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1447 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1467 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1695 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1447 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1467 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1575 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 8, 9, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1811
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08240 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1254 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1007 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1008 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1026 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1135 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 8, 9, 10}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1811
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08241 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1453 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1696 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1453 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1459 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1576 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1696 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 8}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0483
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08242 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1453 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1696 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0140 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1453 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1459 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1576 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1696 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 8}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0483
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08243 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1255 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1010 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1011 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1014 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1020 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1136 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1255 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 8}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0483
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08244 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1697 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1454 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1577 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1697 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0739
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08245 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1697 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1454 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1577 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1697 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0739
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08246 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1697 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1454 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1577 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1697 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 9}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0739
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08247 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1256 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1010 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1015 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1021 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1137 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1256 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 9}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0739
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08248 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1455 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1698 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1455 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1461 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1578 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1251
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08249 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1455 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1698 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1455 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1461 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1578 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1251
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08250 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1579 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0867
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08251 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1579 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0867
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08252 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1579 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0867
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08253 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1699 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1579 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0867
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08254 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1258 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1011 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1017 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1139 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1258 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0867
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08255 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1580 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 10}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1379
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08256 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1580 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 10}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1379
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08257 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1580 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1379
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause08258 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1700 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0042 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1580 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 10}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
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
    have heq := synchronizedFiveFanFin11_fiveSubset_mask1379
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
