module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 69. -/

theorem halfPureSingletonFanFin10_clause15970 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0904 χ) := by
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
  unfold HalfPureSingletonFanFin10Atom0904 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 7, 9}, 6, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {0, 2, 3, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15971 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0653 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0653 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0781
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 3, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15972 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0905 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0067 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0905 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 3, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0781
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 2, 3, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15985 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0667 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0080 at h5
  unfold HalfPureSingletonFanFin10Atom0081 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0667 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 7, 8}, 6, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15986 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0919 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0080 at h5
  unfold HalfPureSingletonFanFin10Atom0081 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0919 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {0, 2, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15987 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0668 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0080 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0668 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 7, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0677
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 2, 5, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15989 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0669 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0669 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15990 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0921 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0076 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0921 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15991 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0673 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0673 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 7, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15992 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0925 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0081 at h5
  unfold HalfPureSingletonFanFin10Atom0082 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0925 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 7, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {0, 2, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16005 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0687 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0687 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 7, 8}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0425
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 3, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16006 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0939 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0032 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0939 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0425
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 3, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16007 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0688 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0688 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 7, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0681
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 3, 5, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16008 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0940 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0940 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 7, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0681
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 3, 5, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16009 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0689 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0689 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0809
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 3, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16010 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0941 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0027 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0941 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0809
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 3, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16011 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0693 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0693 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 7, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0905
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 3, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16012 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0945 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0018 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0945 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 7, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0905
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 3, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16021 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0707 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0027 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0707 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 7, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {0, 5, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16022 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0959 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0027 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0032 at h2
  unfold HalfPureSingletonFanFin10Atom0033 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0112 at h5
  unfold HalfPureSingletonFanFin10Atom0113 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0959 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 7, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16095 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0781 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0076 at h2
  unfold HalfPureSingletonFanFin10Atom0081 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0091 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0106 at h8
  unfold HalfPureSingletonFanFin10Atom0112 at h9
  unfold HalfPureSingletonFanFin10Atom0781 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 5, 8}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0316
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 4, 5, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16096 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom1033 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0076 at h2
  unfold HalfPureSingletonFanFin10Atom0081 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0091 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0106 at h8
  unfold HalfPureSingletonFanFin10Atom0112 at h9
  unfold HalfPureSingletonFanFin10Atom1033 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 5, 8}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0316
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 4, 5, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16097 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0782 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0076 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0091 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0107 at h8
  unfold HalfPureSingletonFanFin10Atom0113 at h9
  unfold HalfPureSingletonFanFin10Atom0782 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 5, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0572
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 4, 5, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16100 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom1038 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0081 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0106 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom1038 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16102 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom1039 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0107 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom1039 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 7, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0668
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 4, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16103 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0788 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0081 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0106 at h7
  unfold HalfPureSingletonFanFin10Atom0107 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0788 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0796
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 4, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16105 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0792 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0081 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0792 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 8}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0428
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16106 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom1044 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0081 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0096 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0112 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom1044 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 8}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0428
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 5, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16107 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0793 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0793 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0684
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 5, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16108 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom1045 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom1045 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0684
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 5, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16109 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0794 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0081 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom0794 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0812
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16110 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom1046 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0076 at h1
  unfold HalfPureSingletonFanFin10Atom0081 at h2
  unfold HalfPureSingletonFanFin10Atom0082 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0112 at h7
  unfold HalfPureSingletonFanFin10Atom0113 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom1046 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 6, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0812
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
