module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 68. -/

theorem halfPureSingletonFanFin10_clause15584 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom1036 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0076 at h2
  unfold HalfPureSingletonFanFin10Atom0078 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0091 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0103 at h8
  unfold HalfPureSingletonFanFin10Atom0112 at h9
  unfold HalfPureSingletonFanFin10Atom1036 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 6, 8}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0348
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 4, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15587 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0786 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0078 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0102 at h7
  unfold HalfPureSingletonFanFin10Atom0103 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom0786 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 7, 8}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0412
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 4, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15588 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom1038 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0078 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0102 at h7
  unfold HalfPureSingletonFanFin10Atom0103 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom1038 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 7, 8}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0412
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 4, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15593 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0795 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0078 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom0795 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 8}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0460
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15594 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom1047 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0078 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom1047 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 8}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0460
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15595 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0796 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0115 at h9
  unfold HalfPureSingletonFanFin10Atom0796 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0716
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15596 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom1048 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0115 at h9
  unfold HalfPureSingletonFanFin10Atom1048 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0716
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15597 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0797 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0797 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0844
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15598 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom1049 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom1049 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0844
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15599 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0798 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0798 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 7, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0908
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15602 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom1057 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0071 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0078 at h3
  unfold HalfPureSingletonFanFin10Atom0101 at h4
  unfold HalfPureSingletonFanFin10Atom0102 at h5
  unfold HalfPureSingletonFanFin10Atom0103 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom1057 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 6, 7, 8}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0468
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 4, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15604 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom1058 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0071 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0101 at h4
  unfold HalfPureSingletonFanFin10Atom0102 at h5
  unfold HalfPureSingletonFanFin10Atom0104 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0115 at h9
  unfold HalfPureSingletonFanFin10Atom1058 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 6, 7, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0724
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 4, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15608 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom1060 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0071 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0102 at h4
  unfold HalfPureSingletonFanFin10Atom0103 at h5
  unfold HalfPureSingletonFanFin10Atom0104 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom1060 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 7, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0916
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 4, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15609 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0813 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0076 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0813 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 6, 7, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0964
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15610 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom1065 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0076 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom1065 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 6, 7, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0964
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15611 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0820 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0091 at h1
  unfold HalfPureSingletonFanFin10Atom0092 at h2
  unfold HalfPureSingletonFanFin10Atom0093 at h3
  unfold HalfPureSingletonFanFin10Atom0101 at h4
  unfold HalfPureSingletonFanFin10Atom0102 at h5
  unfold HalfPureSingletonFanFin10Atom0103 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom0820 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 6, 7, 8}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0472
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 4, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15612 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom1072 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0091 at h1
  unfold HalfPureSingletonFanFin10Atom0092 at h2
  unfold HalfPureSingletonFanFin10Atom0093 at h3
  unfold HalfPureSingletonFanFin10Atom0101 at h4
  unfold HalfPureSingletonFanFin10Atom0102 at h5
  unfold HalfPureSingletonFanFin10Atom0103 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom1072 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 6, 7, 8}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0472
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {3, 4, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15615 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0822 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0091 at h1
  unfold HalfPureSingletonFanFin10Atom0093 at h2
  unfold HalfPureSingletonFanFin10Atom0094 at h3
  unfold HalfPureSingletonFanFin10Atom0101 at h4
  unfold HalfPureSingletonFanFin10Atom0103 at h5
  unfold HalfPureSingletonFanFin10Atom0104 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0822 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 6, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0856
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 4, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15617 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0823 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0093 at h2
  unfold HalfPureSingletonFanFin10Atom0094 at h3
  unfold HalfPureSingletonFanFin10Atom0102 at h4
  unfold HalfPureSingletonFanFin10Atom0103 at h5
  unfold HalfPureSingletonFanFin10Atom0104 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0823 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 7, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0920
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 4, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15619 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0828 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0091 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0093 at h2
  unfold HalfPureSingletonFanFin10Atom0094 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0828 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 6, 7, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0968
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15620 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom1080 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0091 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0093 at h2
  unfold HalfPureSingletonFanFin10Atom0094 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom1080 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 6, 7, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0968
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {3, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15621 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0833 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0101 at h0
  unfold HalfPureSingletonFanFin10Atom0102 at h1
  unfold HalfPureSingletonFanFin10Atom0103 at h2
  unfold HalfPureSingletonFanFin10Atom0104 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom0833 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 6, 7, 8, 9}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0976
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {4, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15622 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom1085 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0101 at h0
  unfold HalfPureSingletonFanFin10Atom0102 at h1
  unfold HalfPureSingletonFanFin10Atom0103 at h2
  unfold HalfPureSingletonFanFin10Atom0104 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0116 at h9
  unfold HalfPureSingletonFanFin10Atom1085 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 6, 7, 8, 9}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0976
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {4, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15961 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0645 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0027 at h2
  unfold HalfPureSingletonFanFin10Atom0031 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0076 at h5
  unfold HalfPureSingletonFanFin10Atom0080 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0095 at h8
  unfold HalfPureSingletonFanFin10Atom0111 at h9
  unfold HalfPureSingletonFanFin10Atom0645 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 5, 7}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0173
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 3, 5, 7}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15962 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0897 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0027 at h2
  unfold HalfPureSingletonFanFin10Atom0031 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0076 at h5
  unfold HalfPureSingletonFanFin10Atom0080 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0095 at h8
  unfold HalfPureSingletonFanFin10Atom0111 at h9
  unfold HalfPureSingletonFanFin10Atom0897 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 5, 7}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0173
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 3, 5, 7}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15963 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0646 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0027 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0076 at h5
  unfold HalfPureSingletonFanFin10Atom0081 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0112 at h9
  unfold HalfPureSingletonFanFin10Atom0646 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 5, 8}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0301
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 3, 5, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15964 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0898 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0027 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0076 at h5
  unfold HalfPureSingletonFanFin10Atom0081 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0112 at h9
  unfold HalfPureSingletonFanFin10Atom0898 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 5, 8}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0301
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 3, 5, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15965 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0647 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0027 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0076 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0113 at h9
  unfold HalfPureSingletonFanFin10Atom0647 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 5, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0557
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 3, 5, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15966 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0899 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0027 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0076 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0113 at h9
  unfold HalfPureSingletonFanFin10Atom0899 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 5, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0557
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 3, 5, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15967 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0651 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0080 at h5
  unfold HalfPureSingletonFanFin10Atom0081 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0651 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 7, 8}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0397
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 3, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15968 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0903 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0080 at h5
  unfold HalfPureSingletonFanFin10Atom0081 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0903 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0397
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 3, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15969 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0652 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0080 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0652 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 7, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0653
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 3, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
