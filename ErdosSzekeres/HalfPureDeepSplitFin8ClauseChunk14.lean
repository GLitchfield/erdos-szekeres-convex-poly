module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 14. -/

theorem halfPureDeepSplitFin8_clause1895 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom256 χ ∧
      ¬HalfPureDeepSplitFin8Atom116 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom116 HalfPureDeepSplitFin8Atom256 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1896 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom256 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom256 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1897 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom116 χ ∧
      HalfPureDeepSplitFin8Atom038 χ ∧
      ¬HalfPureDeepSplitFin8Atom256 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom116 HalfPureDeepSplitFin8Atom256 at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1901 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom257 χ ∧
      ¬HalfPureDeepSplitFin8Atom117 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom117 HalfPureDeepSplitFin8Atom257 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1902 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom257 χ ∧
      ¬HalfPureDeepSplitFin8Atom039 χ ∧
      ¬HalfPureDeepSplitFin8Atom040 χ ∧
      ¬HalfPureDeepSplitFin8Atom046 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom039 HalfPureDeepSplitFin8Atom040 HalfPureDeepSplitFin8Atom046
    HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom257 at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1907 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom258 χ ∧
      ¬HalfPureDeepSplitFin8Atom118 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom118 HalfPureDeepSplitFin8Atom258 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1908 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom258 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom042 χ ∧
      ¬HalfPureDeepSplitFin8Atom044 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom042 HalfPureDeepSplitFin8Atom044
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom258 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1913 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom259 χ ∧
      ¬HalfPureDeepSplitFin8Atom119 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom119 HalfPureDeepSplitFin8Atom259 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1914 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom259 χ ∧
      ¬HalfPureDeepSplitFin8Atom041 χ ∧
      ¬HalfPureDeepSplitFin8Atom043 χ ∧
      ¬HalfPureDeepSplitFin8Atom045 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom041 HalfPureDeepSplitFin8Atom043 HalfPureDeepSplitFin8Atom045
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom259 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1919 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom260 χ ∧
      ¬HalfPureDeepSplitFin8Atom120 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom120 HalfPureDeepSplitFin8Atom260 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1925 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom261 χ ∧
      ¬HalfPureDeepSplitFin8Atom121 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom121 HalfPureDeepSplitFin8Atom261 at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1931 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom262 χ ∧
      ¬HalfPureDeepSplitFin8Atom122 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom122 HalfPureDeepSplitFin8Atom262 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1932 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom262 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom053 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom050
    HalfPureDeepSplitFin8Atom053 HalfPureDeepSplitFin8Atom262 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1937 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom263 χ ∧
      ¬HalfPureDeepSplitFin8Atom123 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom123 HalfPureDeepSplitFin8Atom263 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1938 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom263 χ ∧
      ¬HalfPureDeepSplitFin8Atom047 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom047 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom051
    HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom263 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1940 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom123 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom263 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom123 HalfPureDeepSplitFin8Atom263 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1942 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom123 χ ∧
      HalfPureDeepSplitFin8Atom054 χ ∧
      ¬HalfPureDeepSplitFin8Atom263 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom123 HalfPureDeepSplitFin8Atom263 at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1943 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom264 χ ∧
      ¬HalfPureDeepSplitFin8Atom124 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom124 HalfPureDeepSplitFin8Atom264 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1944 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom264 χ ∧
      ¬HalfPureDeepSplitFin8Atom048 χ ∧
      ¬HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom048 HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom264 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1946 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom049 χ ∧
      ¬HalfPureDeepSplitFin8Atom264 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom049 HalfPureDeepSplitFin8Atom124 HalfPureDeepSplitFin8Atom264 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1948 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom124 χ ∧
      HalfPureDeepSplitFin8Atom055 χ ∧
      ¬HalfPureDeepSplitFin8Atom264 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom124 HalfPureDeepSplitFin8Atom264 at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1949 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom265 χ ∧
      ¬HalfPureDeepSplitFin8Atom125 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom265 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1950 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom265 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom052
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom265 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1951 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom125 χ ∧
      HalfPureDeepSplitFin8Atom050 χ ∧
      ¬HalfPureDeepSplitFin8Atom265 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom125 HalfPureDeepSplitFin8Atom265 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
