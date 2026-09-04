module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 062. -/

theorem fin15Anchored_clause07936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07937 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07943 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0837 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0837 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07945 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0837 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0837 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0100 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0837 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07948 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07950 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07951 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0101 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0838 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07957 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0102 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0839 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07964 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07966 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0103 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0840 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07974 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07975 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07976 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0095 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0841 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07984 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07985 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07986 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0096 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0842 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07993 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0097 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0193 Fin15AnchoredAtom0843 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07996 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07997 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07998 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0098 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0844 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08004 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08005 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0099 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0845 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0846 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0846 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0846 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08016 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0846 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0100 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0846 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08020 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0101 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0847 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08026 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08027 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08029 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0102 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0848 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08034 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08035 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08036 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08037 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0094 Fin15AnchoredAtom0103 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0849 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08044 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08046 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0096 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0850 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08053 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 Fin15AnchoredAtom0851 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08054 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 Fin15AnchoredAtom0851 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 Fin15AnchoredAtom0851 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0097 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0201 Fin15AnchoredAtom0851 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08059 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0098 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0852 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
