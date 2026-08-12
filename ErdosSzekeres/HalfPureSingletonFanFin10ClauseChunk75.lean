module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 75. -/

theorem halfPureSingletonFanFin10_clause17660 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom1066 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0090 at h0
  unfold HalfPureSingletonFanFin10Atom0094 at h1
  unfold HalfPureSingletonFanFin10Atom0097 at h2
  unfold HalfPureSingletonFanFin10Atom0099 at h3
  unfold HalfPureSingletonFanFin10Atom0104 at h4
  unfold HalfPureSingletonFanFin10Atom0107 at h5
  unfold HalfPureSingletonFanFin10Atom0109 at h6
  unfold HalfPureSingletonFanFin10Atom0113 at h7
  unfold HalfPureSingletonFanFin10Atom0115 at h8
  unfold HalfPureSingletonFanFin10Atom0118 at h9
  unfold HalfPureSingletonFanFin10Atom1066 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 5, 6, 7}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0248
      polygon hsub hcard
    subst polygon
    show IsCapSet χ {3, 4, 5, 6, 7}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause17662 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom1067 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0090 at h0
  unfold HalfPureSingletonFanFin10Atom0094 at h1
  unfold HalfPureSingletonFanFin10Atom0097 at h2
  unfold HalfPureSingletonFanFin10Atom0100 at h3
  unfold HalfPureSingletonFanFin10Atom0104 at h4
  unfold HalfPureSingletonFanFin10Atom0107 at h5
  unfold HalfPureSingletonFanFin10Atom0110 at h6
  unfold HalfPureSingletonFanFin10Atom0113 at h7
  unfold HalfPureSingletonFanFin10Atom0116 at h8
  unfold HalfPureSingletonFanFin10Atom0119 at h9
  unfold HalfPureSingletonFanFin10Atom1067 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 4, 5, 6, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {3, 4, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause17667 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom0824 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0094 at h0
  unfold HalfPureSingletonFanFin10Atom0097 at h1
  unfold HalfPureSingletonFanFin10Atom0099 at h2
  unfold HalfPureSingletonFanFin10Atom0100 at h3
  unfold HalfPureSingletonFanFin10Atom0113 at h4
  unfold HalfPureSingletonFanFin10Atom0115 at h5
  unfold HalfPureSingletonFanFin10Atom0116 at h6
  unfold HalfPureSingletonFanFin10Atom0118 at h7
  unfold HalfPureSingletonFanFin10Atom0119 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom0824 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 7, 8}, 9, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {3, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause17668 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom1076 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0094 at h0
  unfold HalfPureSingletonFanFin10Atom0097 at h1
  unfold HalfPureSingletonFanFin10Atom0099 at h2
  unfold HalfPureSingletonFanFin10Atom0100 at h3
  unfold HalfPureSingletonFanFin10Atom0113 at h4
  unfold HalfPureSingletonFanFin10Atom0115 at h5
  unfold HalfPureSingletonFanFin10Atom0116 at h6
  unfold HalfPureSingletonFanFin10Atom0118 at h7
  unfold HalfPureSingletonFanFin10Atom0119 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom1076 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 7, 8}, 9, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause17670 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ ∧
      ¬HalfPureSingletonFanFin10Atom1081 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0104 at h0
  unfold HalfPureSingletonFanFin10Atom0107 at h1
  unfold HalfPureSingletonFanFin10Atom0109 at h2
  unfold HalfPureSingletonFanFin10Atom0110 at h3
  unfold HalfPureSingletonFanFin10Atom0113 at h4
  unfold HalfPureSingletonFanFin10Atom0115 at h5
  unfold HalfPureSingletonFanFin10Atom0116 at h6
  unfold HalfPureSingletonFanFin10Atom0118 at h7
  unfold HalfPureSingletonFanFin10Atom0119 at h8
  unfold HalfPureSingletonFanFin10Atom0120 at h9
  unfold HalfPureSingletonFanFin10Atom1081 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{4, 5, 6, 7, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    show IsCapSet χ {4, 5, 6, 7, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
