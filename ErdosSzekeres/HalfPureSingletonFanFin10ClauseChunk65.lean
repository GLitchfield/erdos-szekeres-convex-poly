module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 65. -/

theorem halfPureSingletonFanFin10_clause14066 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom1076 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0069 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0077 at h5
  unfold HalfPureSingletonFanFin10Atom0078 at h6
  unfold HalfPureSingletonFanFin10Atom0080 at h7
  unfold HalfPureSingletonFanFin10Atom0081 at h8
  unfold HalfPureSingletonFanFin10Atom0083 at h9
  unfold HalfPureSingletonFanFin10Atom1076 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 7, 8}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0488
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {3, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14067 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0825 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0077 at h5
  unfold HalfPureSingletonFanFin10Atom0079 at h6
  unfold HalfPureSingletonFanFin10Atom0080 at h7
  unfold HalfPureSingletonFanFin10Atom0082 at h8
  unfold HalfPureSingletonFanFin10Atom0084 at h9
  unfold HalfPureSingletonFanFin10Atom0825 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 7, 9}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0744
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 5, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14068 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom1077 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0077 at h5
  unfold HalfPureSingletonFanFin10Atom0079 at h6
  unfold HalfPureSingletonFanFin10Atom0080 at h7
  unfold HalfPureSingletonFanFin10Atom0082 at h8
  unfold HalfPureSingletonFanFin10Atom0084 at h9
  unfold HalfPureSingletonFanFin10Atom1077 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 7, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0744
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {3, 5, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14069 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0826 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0078 at h5
  unfold HalfPureSingletonFanFin10Atom0079 at h6
  unfold HalfPureSingletonFanFin10Atom0081 at h7
  unfold HalfPureSingletonFanFin10Atom0082 at h8
  unfold HalfPureSingletonFanFin10Atom0085 at h9
  unfold HalfPureSingletonFanFin10Atom0826 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 8, 9}, 2, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0872
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14070 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom1078 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0078 at h5
  unfold HalfPureSingletonFanFin10Atom0079 at h6
  unfold HalfPureSingletonFanFin10Atom0081 at h7
  unfold HalfPureSingletonFanFin10Atom0082 at h8
  unfold HalfPureSingletonFanFin10Atom0085 at h9
  unfold HalfPureSingletonFanFin10Atom1078 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0872
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {3, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14073 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0828 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0068 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0083 at h7
  unfold HalfPureSingletonFanFin10Atom0084 at h8
  unfold HalfPureSingletonFanFin10Atom0085 at h9
  unfold HalfPureSingletonFanFin10Atom0828 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 6, 7, 8, 9}, 2, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause14074 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom1080 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0068 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0083 at h7
  unfold HalfPureSingletonFanFin10Atom0084 at h8
  unfold HalfPureSingletonFanFin10Atom0085 at h9
  unfold HalfPureSingletonFanFin10Atom1080 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 6, 7, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause14084 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom1085 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0072 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0074 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0083 at h7
  unfold HalfPureSingletonFanFin10Atom0084 at h8
  unfold HalfPureSingletonFanFin10Atom0085 at h9
  unfold HalfPureSingletonFanFin10Atom1085 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 6, 7, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause14086 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom1086 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0076 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0078 at h2
  unfold HalfPureSingletonFanFin10Atom0079 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0083 at h7
  unfold HalfPureSingletonFanFin10Atom0084 at h8
  unfold HalfPureSingletonFanFin10Atom0085 at h9
  unfold HalfPureSingletonFanFin10Atom1086 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{5, 6, 7, 8, 9}, 2, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0992
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {5, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14439 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0665 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0018 at h2
  unfold HalfPureSingletonFanFin10Atom0020 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0067 at h5
  unfold HalfPureSingletonFanFin10Atom0069 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0093 at h8
  unfold HalfPureSingletonFanFin10Atom0096 at h9
  unfold HalfPureSingletonFanFin10Atom0665 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 6, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0357
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14440 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0917 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0018 at h2
  unfold HalfPureSingletonFanFin10Atom0020 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0067 at h5
  unfold HalfPureSingletonFanFin10Atom0069 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0093 at h8
  unfold HalfPureSingletonFanFin10Atom0096 at h9
  unfold HalfPureSingletonFanFin10Atom0917 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 6, 8}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0357
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14441 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0666 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0018 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0067 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0094 at h8
  unfold HalfPureSingletonFanFin10Atom0097 at h9
  unfold HalfPureSingletonFanFin10Atom0666 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 6, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0613
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14442 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0918 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0018 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0067 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0094 at h8
  unfold HalfPureSingletonFanFin10Atom0097 at h9
  unfold HalfPureSingletonFanFin10Atom0918 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 6, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0613
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14443 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0667 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0019 at h2
  unfold HalfPureSingletonFanFin10Atom0020 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0068 at h5
  unfold HalfPureSingletonFanFin10Atom0069 at h6
  unfold HalfPureSingletonFanFin10Atom0092 at h7
  unfold HalfPureSingletonFanFin10Atom0093 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0667 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 7, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0421
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14447 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0669 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0069 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0093 at h7
  unfold HalfPureSingletonFanFin10Atom0094 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0669 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0805
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14448 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0921 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0017 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0069 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0093 at h7
  unfold HalfPureSingletonFanFin10Atom0094 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0921 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0805
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14449 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0670 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0019 at h2
  unfold HalfPureSingletonFanFin10Atom0020 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0068 at h5
  unfold HalfPureSingletonFanFin10Atom0069 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0670 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 6, 7, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0453
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14450 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0922 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0019 at h2
  unfold HalfPureSingletonFanFin10Atom0020 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0068 at h5
  unfold HalfPureSingletonFanFin10Atom0069 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0922 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 6, 7, 8}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0453
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14453 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0672 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0069 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0672 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 6, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0837
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14454 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0924 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0069 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0924 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0837
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14455 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0673 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0019 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0068 at h4
  unfold HalfPureSingletonFanFin10Atom0069 at h5
  unfold HalfPureSingletonFanFin10Atom0070 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0673 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 7, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0901
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14481 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0706 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0017 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0706 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 6, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0865
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14482 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0958 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0017 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0958 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0865
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14484 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0959 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0017 at h0
  unfold HalfPureSingletonFanFin10Atom0019 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0959 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 7, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0929
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 5, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14485 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0708 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0019 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0708 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 6, 7, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0961
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14486 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0960 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0019 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0960 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 6, 7, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0961
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 6, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14557 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0799 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0066 at h1
  unfold HalfPureSingletonFanFin10Atom0067 at h2
  unfold HalfPureSingletonFanFin10Atom0068 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0088 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0092 at h8
  unfold HalfPureSingletonFanFin10Atom0095 at h9
  unfold HalfPureSingletonFanFin10Atom0799 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 5, 6, 7}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0244
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 4, 5, 6, 7}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14559 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0800 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0066 at h1
  unfold HalfPureSingletonFanFin10Atom0067 at h2
  unfold HalfPureSingletonFanFin10Atom0069 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0091 at h7
  unfold HalfPureSingletonFanFin10Atom0093 at h8
  unfold HalfPureSingletonFanFin10Atom0096 at h9
  unfold HalfPureSingletonFanFin10Atom0800 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 5, 6, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0372
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 4, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14563 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0802 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0066 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0069 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0088 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0092 at h7
  unfold HalfPureSingletonFanFin10Atom0093 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0802 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 5, 7, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0436
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 4, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14568 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom1056 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0066 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0093 at h7
  unfold HalfPureSingletonFanFin10Atom0094 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom1056 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 5, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0820
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 4, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14569 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0805 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0069 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0088 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0805 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 6, 7, 8}, 3, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14571 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0806 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0088 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0099 at h9
  unfold HalfPureSingletonFanFin10Atom0806 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 6, 7, 9}, 3, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
