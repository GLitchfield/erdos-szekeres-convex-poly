module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 077. -/

theorem fin15Anchored_clause09856 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09862 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09863 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09864 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09866 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09867 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1089 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09873 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09874 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09875 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1090 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1091 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1091 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09882 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1092 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1092 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09883 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09884 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09885 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09886 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1093 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09892 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09894 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1094 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09903 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09904 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09906 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1095 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09912 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1096 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09913 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1096 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1096 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1096 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1097 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1097 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1097 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1097 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1098 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1098 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09921 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1098 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1098 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1098 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1098 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1098 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1098 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09924 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1099 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09933 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1100 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09943 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09945 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1101 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09953 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1102 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09954 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1102 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1102 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1102 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1102 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09960 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09961 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1103 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1104 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1104 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1104 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1104 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1105 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 Fin15AnchoredAtom1106 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09979 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 Fin15AnchoredAtom1106 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09980 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 Fin15AnchoredAtom1106 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09981 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 Fin15AnchoredAtom1106 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 Fin15AnchoredAtom1106 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 Fin15AnchoredAtom1106 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
