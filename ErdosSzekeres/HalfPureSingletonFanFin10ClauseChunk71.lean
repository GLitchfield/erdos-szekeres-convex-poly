module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 71. -/

theorem halfPureSingletonFanFin10_clause16501 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0669 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0013 at h0
  unfold HalfPureSingletonFanFin10Atom0028 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0077 at h4
  unfold HalfPureSingletonFanFin10Atom0083 at h5
  unfold HalfPureSingletonFanFin10Atom0084 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0669 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 5, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16503 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0672 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0013 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0083 at h5
  unfold HalfPureSingletonFanFin10Atom0084 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0672 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 6, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16504 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0924 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0013 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0080 at h4
  unfold HalfPureSingletonFanFin10Atom0083 at h5
  unfold HalfPureSingletonFanFin10Atom0084 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0924 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 2, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16518 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0937 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0019 at h0
  unfold HalfPureSingletonFanFin10Atom0028 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0034 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0098 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0114 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0937 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 6, 8}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0361
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 3, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16519 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0686 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0019 at h0
  unfold HalfPureSingletonFanFin10Atom0028 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0686 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 6, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0617
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 3, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16520 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0938 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0019 at h0
  unfold HalfPureSingletonFanFin10Atom0028 at h1
  unfold HalfPureSingletonFanFin10Atom0031 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0938 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 6, 9}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0617
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {0, 3, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16521 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0689 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0019 at h0
  unfold HalfPureSingletonFanFin10Atom0028 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0689 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16522 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0941 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0019 at h0
  unfold HalfPureSingletonFanFin10Atom0028 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0941 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16523 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0692 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0019 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0692 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 6, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0841
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {0, 3, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16533 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0706 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0028 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0114 at h5
  unfold HalfPureSingletonFanFin10Atom0115 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0706 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 6, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16534 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0958 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0028 at h0
  unfold HalfPureSingletonFanFin10Atom0031 at h1
  unfold HalfPureSingletonFanFin10Atom0034 at h2
  unfold HalfPureSingletonFanFin10Atom0035 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0114 at h5
  unfold HalfPureSingletonFanFin10Atom0115 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0958 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 5, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16605 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0779 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0080 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0095 at h6
  unfold HalfPureSingletonFanFin10Atom0102 at h7
  unfold HalfPureSingletonFanFin10Atom0105 at h8
  unfold HalfPureSingletonFanFin10Atom0111 at h9
  unfold HalfPureSingletonFanFin10Atom0779 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 5, 6}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0124
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 4, 5, 6}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16607 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0781 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0083 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0098 at h6
  unfold HalfPureSingletonFanFin10Atom0102 at h7
  unfold HalfPureSingletonFanFin10Atom0108 at h8
  unfold HalfPureSingletonFanFin10Atom0114 at h9
  unfold HalfPureSingletonFanFin10Atom0781 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 5, 8}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16609 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0782 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0077 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0102 at h7
  unfold HalfPureSingletonFanFin10Atom0109 at h8
  unfold HalfPureSingletonFanFin10Atom0115 at h9
  unfold HalfPureSingletonFanFin10Atom0782 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 5, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16611 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0784 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0083 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0098 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0108 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0784 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 6, 8}, 7, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {2, 3, 4, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16613 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0785 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0109 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0785 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 4, 6, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0604
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 4, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16617 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0790 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0083 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0098 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0114 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0790 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 8}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0364
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16618 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom1042 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0083 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0098 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0114 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom1042 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 8}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0364
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16619 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0791 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0791 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0620
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16620 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom1043 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0095 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom1043 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 9}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0620
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16621 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0794 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0083 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0794 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16622 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom1046 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0083 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0092 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom1046 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16623 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0797 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0080 at h1
  unfold HalfPureSingletonFanFin10Atom0083 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0797 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16624 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom1049 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0068 at h0
  unfold HalfPureSingletonFanFin10Atom0080 at h1
  unfold HalfPureSingletonFanFin10Atom0083 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0098 at h5
  unfold HalfPureSingletonFanFin10Atom0099 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom1049 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause16625 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0800 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0073 at h0
  unfold HalfPureSingletonFanFin10Atom0077 at h1
  unfold HalfPureSingletonFanFin10Atom0080 at h2
  unfold HalfPureSingletonFanFin10Atom0083 at h3
  unfold HalfPureSingletonFanFin10Atom0102 at h4
  unfold HalfPureSingletonFanFin10Atom0105 at h5
  unfold HalfPureSingletonFanFin10Atom0108 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0114 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0800 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 5, 6, 8}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16633 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0811 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0077 at h0
  unfold HalfPureSingletonFanFin10Atom0080 at h1
  unfold HalfPureSingletonFanFin10Atom0083 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0114 at h5
  unfold HalfPureSingletonFanFin10Atom0115 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0811 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0868
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16634 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom1063 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0077 at h0
  unfold HalfPureSingletonFanFin10Atom0080 at h1
  unfold HalfPureSingletonFanFin10Atom0083 at h2
  unfold HalfPureSingletonFanFin10Atom0084 at h3
  unfold HalfPureSingletonFanFin10Atom0111 at h4
  unfold HalfPureSingletonFanFin10Atom0114 at h5
  unfold HalfPureSingletonFanFin10Atom0115 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom1063 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0868
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16635 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0815 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0088 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0095 at h2
  unfold HalfPureSingletonFanFin10Atom0098 at h3
  unfold HalfPureSingletonFanFin10Atom0102 at h4
  unfold HalfPureSingletonFanFin10Atom0105 at h5
  unfold HalfPureSingletonFanFin10Atom0108 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0114 at h8
  unfold HalfPureSingletonFanFin10Atom0117 at h9
  unfold HalfPureSingletonFanFin10Atom0815 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 5, 6, 8}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0376
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 4, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16637 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0816 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0088 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0095 at h2
  unfold HalfPureSingletonFanFin10Atom0099 at h3
  unfold HalfPureSingletonFanFin10Atom0102 at h4
  unfold HalfPureSingletonFanFin10Atom0105 at h5
  unfold HalfPureSingletonFanFin10Atom0109 at h6
  unfold HalfPureSingletonFanFin10Atom0111 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom0816 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 5, 6, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0632
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 4, 5, 6, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16639 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0819 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0088 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0098 at h2
  unfold HalfPureSingletonFanFin10Atom0099 at h3
  unfold HalfPureSingletonFanFin10Atom0102 at h4
  unfold HalfPureSingletonFanFin10Atom0108 at h5
  unfold HalfPureSingletonFanFin10Atom0109 at h6
  unfold HalfPureSingletonFanFin10Atom0114 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0819 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 5, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0824
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {3, 4, 5, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause16641 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0822 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0088 at h0
  unfold HalfPureSingletonFanFin10Atom0095 at h1
  unfold HalfPureSingletonFanFin10Atom0098 at h2
  unfold HalfPureSingletonFanFin10Atom0099 at h3
  unfold HalfPureSingletonFanFin10Atom0105 at h4
  unfold HalfPureSingletonFanFin10Atom0108 at h5
  unfold HalfPureSingletonFanFin10Atom0109 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0822 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 6, 8, 9}, 7, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause16642 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom1074 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0088 at h0
  unfold HalfPureSingletonFanFin10Atom0095 at h1
  unfold HalfPureSingletonFanFin10Atom0098 at h2
  unfold HalfPureSingletonFanFin10Atom0099 at h3
  unfold HalfPureSingletonFanFin10Atom0105 at h4
  unfold HalfPureSingletonFanFin10Atom0108 at h5
  unfold HalfPureSingletonFanFin10Atom0109 at h6
  unfold HalfPureSingletonFanFin10Atom0117 at h7
  unfold HalfPureSingletonFanFin10Atom0118 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom1074 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 6, 8, 9}, 7, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {3, 4, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
