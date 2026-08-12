module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 66. -/

theorem halfPureSingletonFanFin10_clause14573 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0807 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0807 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 6, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0852
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 4, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14574 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom1059 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom1059 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0852
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 4, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14575 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0808 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0068 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0808 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 7, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {2, 4, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14576 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom1060 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0068 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom1060 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 4, 7, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause14577 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0809 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0069 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0809 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0484
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14578 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom1061 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0069 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom1061 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 8}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0484
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14579 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0810 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0099 at h9
  unfold HalfPureSingletonFanFin10Atom0810 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0740
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 5, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14580 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom1062 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0068 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0099 at h9
  unfold HalfPureSingletonFanFin10Atom1062 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 9}, 3, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0740
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 5, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14581 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0811 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0811 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause14582 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom1063 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0066 at h0
  unfold HalfPureSingletonFanFin10Atom0067 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom1063 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause14585 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0813 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0068 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0813 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 6, 7, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause14586 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom1065 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0067 at h0
  unfold HalfPureSingletonFanFin10Atom0068 at h1
  unfold HalfPureSingletonFanFin10Atom0069 at h2
  unfold HalfPureSingletonFanFin10Atom0070 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom1065 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 6, 7, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause14587 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0829 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0087 at h1
  unfold HalfPureSingletonFanFin10Atom0088 at h2
  unfold HalfPureSingletonFanFin10Atom0089 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0093 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0096 at h8
  unfold HalfPureSingletonFanFin10Atom0098 at h9
  unfold HalfPureSingletonFanFin10Atom0829 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 5, 6, 7, 8}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0496
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {4, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14589 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0830 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0087 at h1
  unfold HalfPureSingletonFanFin10Atom0088 at h2
  unfold HalfPureSingletonFanFin10Atom0090 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0092 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0095 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0099 at h9
  unfold HalfPureSingletonFanFin10Atom0830 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 5, 6, 7, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0752
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {4, 5, 6, 7, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14591 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0831 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0086 at h0
  unfold HalfPureSingletonFanFin10Atom0087 at h1
  unfold HalfPureSingletonFanFin10Atom0089 at h2
  unfold HalfPureSingletonFanFin10Atom0090 at h3
  unfold HalfPureSingletonFanFin10Atom0091 at h4
  unfold HalfPureSingletonFanFin10Atom0093 at h5
  unfold HalfPureSingletonFanFin10Atom0094 at h6
  unfold HalfPureSingletonFanFin10Atom0096 at h7
  unfold HalfPureSingletonFanFin10Atom0097 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0831 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 5, 6, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0880
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {4, 5, 6, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause14595 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0833 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0087 at h0
  unfold HalfPureSingletonFanFin10Atom0088 at h1
  unfold HalfPureSingletonFanFin10Atom0089 at h2
  unfold HalfPureSingletonFanFin10Atom0090 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom0833 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 6, 7, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause14598 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom1086 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0091 at h0
  unfold HalfPureSingletonFanFin10Atom0092 at h1
  unfold HalfPureSingletonFanFin10Atom0093 at h2
  unfold HalfPureSingletonFanFin10Atom0094 at h3
  unfold HalfPureSingletonFanFin10Atom0095 at h4
  unfold HalfPureSingletonFanFin10Atom0096 at h5
  unfold HalfPureSingletonFanFin10Atom0097 at h6
  unfold HalfPureSingletonFanFin10Atom0098 at h7
  unfold HalfPureSingletonFanFin10Atom0099 at h8
  unfold HalfPureSingletonFanFin10Atom0100 at h9
  unfold HalfPureSingletonFanFin10Atom1086 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{5, 6, 7, 8, 9}, 3, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15069 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0789 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0072 at h2
  unfold HalfPureSingletonFanFin10Atom0073 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0088 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0102 at h8
  unfold HalfPureSingletonFanFin10Atom0105 at h9
  unfold HalfPureSingletonFanFin10Atom0789 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 7}, 4, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0236
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 3, 5, 6, 7}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15070 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom1041 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0072 at h2
  unfold HalfPureSingletonFanFin10Atom0073 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0088 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0102 at h8
  unfold HalfPureSingletonFanFin10Atom0105 at h9
  unfold HalfPureSingletonFanFin10Atom1041 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 7}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0236
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 3, 5, 6, 7}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15071 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0790 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0072 at h2
  unfold HalfPureSingletonFanFin10Atom0074 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0103 at h8
  unfold HalfPureSingletonFanFin10Atom0106 at h9
  unfold HalfPureSingletonFanFin10Atom0790 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 8}, 4, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15072 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom1042 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0072 at h2
  unfold HalfPureSingletonFanFin10Atom0074 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0103 at h8
  unfold HalfPureSingletonFanFin10Atom0106 at h9
  unfold HalfPureSingletonFanFin10Atom1042 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 8}, 4, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15073 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0791 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0072 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0104 at h8
  unfold HalfPureSingletonFanFin10Atom0107 at h9
  unfold HalfPureSingletonFanFin10Atom0791 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 9}, 4, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15074 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom1043 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0072 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0087 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0101 at h7
  unfold HalfPureSingletonFanFin10Atom0104 at h8
  unfold HalfPureSingletonFanFin10Atom0107 at h9
  unfold HalfPureSingletonFanFin10Atom1043 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 9}, 4, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15076 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom1044 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0073 at h2
  unfold HalfPureSingletonFanFin10Atom0074 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0088 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0102 at h7
  unfold HalfPureSingletonFanFin10Atom0103 at h8
  unfold HalfPureSingletonFanFin10Atom0108 at h9
  unfold HalfPureSingletonFanFin10Atom1044 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 8}, 4, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15079 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0794 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0071 at h1
  unfold HalfPureSingletonFanFin10Atom0074 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0086 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0103 at h7
  unfold HalfPureSingletonFanFin10Atom0104 at h8
  unfold HalfPureSingletonFanFin10Atom0110 at h9
  unfold HalfPureSingletonFanFin10Atom0794 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 4, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15082 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom1047 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0073 at h2
  unfold HalfPureSingletonFanFin10Atom0074 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0088 at h5
  unfold HalfPureSingletonFanFin10Atom0089 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0106 at h8
  unfold HalfPureSingletonFanFin10Atom0108 at h9
  unfold HalfPureSingletonFanFin10Atom1047 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 8}, 4, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15084 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom1048 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0073 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0088 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0107 at h8
  unfold HalfPureSingletonFanFin10Atom0109 at h9
  unfold HalfPureSingletonFanFin10Atom1048 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 9}, 4, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15085 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0087 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0107 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0797 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0074 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0106 at h7
  unfold HalfPureSingletonFanFin10Atom0107 at h8
  unfold HalfPureSingletonFanFin10Atom0110 at h9
  unfold HalfPureSingletonFanFin10Atom0797 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 4, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15086 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom1049 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0074 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0087 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0106 at h7
  unfold HalfPureSingletonFanFin10Atom0107 at h8
  unfold HalfPureSingletonFanFin10Atom0110 at h9
  unfold HalfPureSingletonFanFin10Atom1049 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause15087 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0798 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0074 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0108 at h7
  unfold HalfPureSingletonFanFin10Atom0109 at h8
  unfold HalfPureSingletonFanFin10Atom0110 at h9
  unfold HalfPureSingletonFanFin10Atom0798 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 7, 8, 9}, 4, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause15088 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0065 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom1050 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0065 at h0
  unfold HalfPureSingletonFanFin10Atom0073 at h1
  unfold HalfPureSingletonFanFin10Atom0074 at h2
  unfold HalfPureSingletonFanFin10Atom0075 at h3
  unfold HalfPureSingletonFanFin10Atom0088 at h4
  unfold HalfPureSingletonFanFin10Atom0089 at h5
  unfold HalfPureSingletonFanFin10Atom0090 at h6
  unfold HalfPureSingletonFanFin10Atom0108 at h7
  unfold HalfPureSingletonFanFin10Atom0109 at h8
  unfold HalfPureSingletonFanFin10Atom0110 at h9
  unfold HalfPureSingletonFanFin10Atom1050 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 7, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {2, 3, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause15090 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0102 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom1061 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0071 at h0
  unfold HalfPureSingletonFanFin10Atom0072 at h1
  unfold HalfPureSingletonFanFin10Atom0073 at h2
  unfold HalfPureSingletonFanFin10Atom0074 at h3
  unfold HalfPureSingletonFanFin10Atom0101 at h4
  unfold HalfPureSingletonFanFin10Atom0102 at h5
  unfold HalfPureSingletonFanFin10Atom0103 at h6
  unfold HalfPureSingletonFanFin10Atom0105 at h7
  unfold HalfPureSingletonFanFin10Atom0106 at h8
  unfold HalfPureSingletonFanFin10Atom0108 at h9
  unfold HalfPureSingletonFanFin10Atom1061 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 8}, 4, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0484
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {2, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
