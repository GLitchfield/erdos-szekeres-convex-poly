module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 63. -/

theorem halfPureSingletonFanFin10_clause12809 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {3, 5, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0307
    HalfPureSingletonFanFin10Atom0308 HalfPureSingletonFanFin10Atom0309
    HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0311
    HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0313
    HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0315
    HalfPureSingletonFanFin10Atom0326 HalfPureSingletonFanFin10Atom0327
    HalfPureSingletonFanFin10Atom0328 HalfPureSingletonFanFin10Atom0329
    HalfPureSingletonFanFin10Atom0330 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12971 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0789 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0013 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0018 at h5
  unfold HalfPureSingletonFanFin10Atom0019 at h6
  unfold HalfPureSingletonFanFin10Atom0027 at h7
  unfold HalfPureSingletonFanFin10Atom0028 at h8
  unfold HalfPureSingletonFanFin10Atom0031 at h9
  unfold HalfPureSingletonFanFin10Atom0789 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 7}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12972 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom1041 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0013 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0018 at h5
  unfold HalfPureSingletonFanFin10Atom0019 at h6
  unfold HalfPureSingletonFanFin10Atom0027 at h7
  unfold HalfPureSingletonFanFin10Atom0028 at h8
  unfold HalfPureSingletonFanFin10Atom0031 at h9
  unfold HalfPureSingletonFanFin10Atom1041 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 7}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12973 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0790 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0018 at h5
  unfold HalfPureSingletonFanFin10Atom0020 at h6
  unfold HalfPureSingletonFanFin10Atom0027 at h7
  unfold HalfPureSingletonFanFin10Atom0029 at h8
  unfold HalfPureSingletonFanFin10Atom0032 at h9
  unfold HalfPureSingletonFanFin10Atom0790 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 8}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12974 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom1042 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0018 at h5
  unfold HalfPureSingletonFanFin10Atom0020 at h6
  unfold HalfPureSingletonFanFin10Atom0027 at h7
  unfold HalfPureSingletonFanFin10Atom0029 at h8
  unfold HalfPureSingletonFanFin10Atom0032 at h9
  unfold HalfPureSingletonFanFin10Atom1042 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 8}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12975 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0791 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0018 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0027 at h7
  unfold HalfPureSingletonFanFin10Atom0030 at h8
  unfold HalfPureSingletonFanFin10Atom0033 at h9
  unfold HalfPureSingletonFanFin10Atom0791 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12976 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom1043 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0018 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0027 at h7
  unfold HalfPureSingletonFanFin10Atom0030 at h8
  unfold HalfPureSingletonFanFin10Atom0033 at h9
  unfold HalfPureSingletonFanFin10Atom1043 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 6, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12977 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0792 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0020 at h6
  unfold HalfPureSingletonFanFin10Atom0028 at h7
  unfold HalfPureSingletonFanFin10Atom0029 at h8
  unfold HalfPureSingletonFanFin10Atom0034 at h9
  unfold HalfPureSingletonFanFin10Atom0792 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 8}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12978 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom1044 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0020 at h6
  unfold HalfPureSingletonFanFin10Atom0028 at h7
  unfold HalfPureSingletonFanFin10Atom0029 at h8
  unfold HalfPureSingletonFanFin10Atom0034 at h9
  unfold HalfPureSingletonFanFin10Atom1044 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 8}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12980 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom1045 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0028 at h7
  unfold HalfPureSingletonFanFin10Atom0030 at h8
  unfold HalfPureSingletonFanFin10Atom0035 at h9
  unfold HalfPureSingletonFanFin10Atom1045 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 7, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12981 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0794 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0020 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0029 at h7
  unfold HalfPureSingletonFanFin10Atom0030 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0794 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12982 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom1046 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0017 at h4
  unfold HalfPureSingletonFanFin10Atom0020 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0029 at h7
  unfold HalfPureSingletonFanFin10Atom0030 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom1046 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 5, 8, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12983 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0795 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0018 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0020 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0032 at h8
  unfold HalfPureSingletonFanFin10Atom0034 at h9
  unfold HalfPureSingletonFanFin10Atom0795 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 8}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12984 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom1047 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0018 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0020 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0032 at h8
  unfold HalfPureSingletonFanFin10Atom0034 at h9
  unfold HalfPureSingletonFanFin10Atom1047 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 8}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12985 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0796 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0018 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0035 at h9
  unfold HalfPureSingletonFanFin10Atom0796 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12986 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom1048 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0018 at h4
  unfold HalfPureSingletonFanFin10Atom0019 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0035 at h9
  unfold HalfPureSingletonFanFin10Atom1048 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 7, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12987 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0797 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0018 at h4
  unfold HalfPureSingletonFanFin10Atom0020 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0032 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0797 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12988 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom1049 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0018 at h4
  unfold HalfPureSingletonFanFin10Atom0020 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0032 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom1049 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 6, 8, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause12989 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0798 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0013 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0019 at h4
  unfold HalfPureSingletonFanFin10Atom0020 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0034 at h7
  unfold HalfPureSingletonFanFin10Atom0035 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0798 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 7, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause12990 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0019 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom1050 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0013 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0019 at h4
  unfold HalfPureSingletonFanFin10Atom0020 at h5
  unfold HalfPureSingletonFanFin10Atom0021 at h6
  unfold HalfPureSingletonFanFin10Atom0034 at h7
  unfold HalfPureSingletonFanFin10Atom0035 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom1050 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 3, 7, 8, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause13011 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0809 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0028 at h5
  unfold HalfPureSingletonFanFin10Atom0029 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0032 at h8
  unfold HalfPureSingletonFanFin10Atom0034 at h9
  unfold HalfPureSingletonFanFin10Atom0809 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 8}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause13012 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom1061 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0028 at h5
  unfold HalfPureSingletonFanFin10Atom0029 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0032 at h8
  unfold HalfPureSingletonFanFin10Atom0034 at h9
  unfold HalfPureSingletonFanFin10Atom1061 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 8}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause13013 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0810 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0028 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0035 at h9
  unfold HalfPureSingletonFanFin10Atom0810 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause13014 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom1062 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0013 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0028 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0031 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0035 at h9
  unfold HalfPureSingletonFanFin10Atom1062 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 7, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause13015 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0811 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0029 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0032 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0811 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause13016 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom1063 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0012 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0029 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0032 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom1063 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 6, 8, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause13017 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0812 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0011 at h0
  unfold HalfPureSingletonFanFin10Atom0013 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0028 at h4
  unfold HalfPureSingletonFanFin10Atom0029 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0034 at h7
  unfold HalfPureSingletonFanFin10Atom0035 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0812 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 5, 7, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all
  · intro polygon hsub hcard hstrong
    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask0932
      polygon hsub hcard
    subst polygon
    show IsCupSet χ {2, 5, 7, 8, 9}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

theorem halfPureSingletonFanFin10_clause13019 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0813 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0013 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0031 at h4
  unfold HalfPureSingletonFanFin10Atom0032 at h5
  unfold HalfPureSingletonFanFin10Atom0033 at h6
  unfold HalfPureSingletonFanFin10Atom0034 at h7
  unfold HalfPureSingletonFanFin10Atom0035 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0813 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 6, 7, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause13020 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0034 χ ∧
      ¬HalfPureSingletonFanFin10Atom0035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom1065 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0012 at h0
  unfold HalfPureSingletonFanFin10Atom0013 at h1
  unfold HalfPureSingletonFanFin10Atom0014 at h2
  unfold HalfPureSingletonFanFin10Atom0015 at h3
  unfold HalfPureSingletonFanFin10Atom0031 at h4
  unfold HalfPureSingletonFanFin10Atom0032 at h5
  unfold HalfPureSingletonFanFin10Atom0033 at h6
  unfold HalfPureSingletonFanFin10Atom0034 at h7
  unfold HalfPureSingletonFanFin10Atom0035 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom1065 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{2, 6, 7, 8, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause13045 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0826 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0017 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0029 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0032 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom0826 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 8, 9}, 0, by decide, by decide, Or.inl ?_⟩
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

theorem halfPureSingletonFanFin10_clause13046 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom1078 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0017 at h0
  unfold HalfPureSingletonFanFin10Atom0018 at h1
  unfold HalfPureSingletonFanFin10Atom0020 at h2
  unfold HalfPureSingletonFanFin10Atom0021 at h3
  unfold HalfPureSingletonFanFin10Atom0027 at h4
  unfold HalfPureSingletonFanFin10Atom0029 at h5
  unfold HalfPureSingletonFanFin10Atom0030 at h6
  unfold HalfPureSingletonFanFin10Atom0032 at h7
  unfold HalfPureSingletonFanFin10Atom0033 at h8
  unfold HalfPureSingletonFanFin10Atom0036 at h9
  unfold HalfPureSingletonFanFin10Atom1078 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{3, 5, 6, 8, 9}, 0, by decide, by decide, Or.inr ?_⟩
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

theorem halfPureSingletonFanFin10_clause13927 (χ : TripleColoring 10)
    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :
    ¬(¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0685 χ) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  unfold HalfPureSingletonFanFin10Atom0009 at h0
  unfold HalfPureSingletonFanFin10Atom0011 at h1
  unfold HalfPureSingletonFanFin10Atom0012 at h2
  unfold HalfPureSingletonFanFin10Atom0014 at h3
  unfold HalfPureSingletonFanFin10Atom0066 at h4
  unfold HalfPureSingletonFanFin10Atom0067 at h5
  unfold HalfPureSingletonFanFin10Atom0069 at h6
  unfold HalfPureSingletonFanFin10Atom0076 at h7
  unfold HalfPureSingletonFanFin10Atom0078 at h8
  unfold HalfPureSingletonFanFin10Atom0081 at h9
  unfold HalfPureSingletonFanFin10Atom0685 at h10
  apply hno
  unfold HalfPureSingletonFanFin10Conclusion
  refine ⟨{0, 3, 5, 6, 8}, 2, by decide, by decide, Or.inl ?_⟩
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
    show IsCupSet χ {0, 3, 5, 6, 8}
    by_contra hnotPure
    apply h10
    exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
