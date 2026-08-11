module

public import ErdosSzekeres.HalfPureDeepSplitFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained LRAT leaf chunk 7. -/

theorem halfPureDeepSplitFin8_clause0916 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom101 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom046 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom046 HalfPureDeepSplitFin8Atom101 at hbad
  cases hcolor0 : χ ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0921 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom102 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom102 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0922 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom102 χ ∧
      ¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom028 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom102 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0937 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom104 χ ∧
      HalfPureDeepSplitFin8Atom027 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom104 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0938 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom104 χ ∧
      ¬HalfPureDeepSplitFin8Atom027 χ ∧
      HalfPureDeepSplitFin8Atom030 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom027 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom104 at hbad
  cases hcolor0 : χ ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0945 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom105 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom029 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom105 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0946 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom105 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom029 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom105 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0947 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom105 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom050 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom050 HalfPureDeepSplitFin8Atom105 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0953 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom106 χ ∧
      HalfPureDeepSplitFin8Atom028 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom106 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0954 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom106 χ ∧
      ¬HalfPureDeepSplitFin8Atom028 χ ∧
      HalfPureDeepSplitFin8Atom030 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom028 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom106 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0955 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom106 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      ¬HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom106 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0956 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom106 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom051 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom051 HalfPureDeepSplitFin8Atom106 at hbad
  cases hcolor0 : χ ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0961 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom107 χ ∧
      HalfPureDeepSplitFin8Atom029 χ ∧
      ¬HalfPureDeepSplitFin8Atom030 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom029 HalfPureDeepSplitFin8Atom030 HalfPureDeepSplitFin8Atom107 at hbad
  cases hcolor0 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0963 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom107 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom052 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom052 HalfPureDeepSplitFin8Atom107 at hbad
  cases hcolor0 : χ ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0969 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom108 χ ∧
      HalfPureDeepSplitFin8Atom031 χ ∧
      ¬HalfPureDeepSplitFin8Atom032 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom031 HalfPureDeepSplitFin8Atom032 HalfPureDeepSplitFin8Atom108 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0980 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom109 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom054 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom054 HalfPureDeepSplitFin8Atom109 at hbad
  cases hcolor0 : χ ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0987 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom110 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom110 at hbad
  cases hcolor0 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0988 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom110 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom055 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom055 HalfPureDeepSplitFin8Atom110 at hbad
  cases hcolor0 : χ ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0993 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom111 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      ¬HalfPureDeepSplitFin8Atom035 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom111 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0994 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom111 χ ∧
      ¬HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom111 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0995 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom111 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      ¬HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom111 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause0996 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom111 χ ∧
      ¬HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom036 HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom111 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1000 (χ : TripleColoring 8) :
    ¬(¬HalfPureDeepSplitFin8Atom111 χ ∧
      HalfPureDeepSplitFin8Atom034 χ ∧
      HalfPureDeepSplitFin8Atom035 χ ∧
      HalfPureDeepSplitFin8Atom036 χ ∧
      HalfPureDeepSplitFin8Atom056 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom034 HalfPureDeepSplitFin8Atom035 HalfPureDeepSplitFin8Atom036
    HalfPureDeepSplitFin8Atom056 HalfPureDeepSplitFin8Atom111 at hbad
  cases hcolor0 : χ ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

theorem halfPureDeepSplitFin8_clause1001 (χ : TripleColoring 8) :
    ¬(HalfPureDeepSplitFin8Atom112 χ ∧
      HalfPureDeepSplitFin8Atom037 χ ∧
      ¬HalfPureDeepSplitFin8Atom038 χ) := by
  intro hbad
  unfold HalfPureDeepSplitFin8Atom037 HalfPureDeepSplitFin8Atom038 HalfPureDeepSplitFin8Atom112 at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,
            halfPureDeepSplitFin8_isCupSet_four_iff,
            halfPureDeepSplitFin8_isCapSet_four_iff]

end ErdosSzekeres

end
