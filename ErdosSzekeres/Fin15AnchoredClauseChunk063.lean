module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 063. -/

theorem fin15Anchored_clause08064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
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

theorem fin15Anchored_clause08065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
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

theorem fin15Anchored_clause08066 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0099 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0853 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08075 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08077 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08078 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0100 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0854 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08083 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0101 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0855 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08095 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0102 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0856 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0095 Fin15AnchoredAtom0103 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0857 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0858 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0097 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0208 Fin15AnchoredAtom0858 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0098 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0859 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08120 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0099 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0860 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0861 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0100 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0211 Fin15AnchoredAtom0861 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0861 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0100 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0211 Fin15AnchoredAtom0861 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0101 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0862 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08144 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0102 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0863 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08150 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0096 Fin15AnchoredAtom0103 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0864 at hbad
  cases hcolor0 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0098 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0215 Fin15AnchoredAtom0865 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0098 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0215 Fin15AnchoredAtom0865 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0098 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0215 Fin15AnchoredAtom0865 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0098 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0215 Fin15AnchoredAtom0865 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0099 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0866 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0099 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0866 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0099 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0866 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0099 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0866 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0099 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0866 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0099 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0866 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0101 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0218 Fin15AnchoredAtom0868 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0101 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0218 Fin15AnchoredAtom0868 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0101 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0218 Fin15AnchoredAtom0868 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08173 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0103 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0220 Fin15AnchoredAtom0870 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0097 Fin15AnchoredAtom0103 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0220 Fin15AnchoredAtom0870 at hbad
  cases hcolor0 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08175 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08176 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0099 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0871 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0100 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0872 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0100 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0872 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0100 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0872 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0100 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0872 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0100 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0872 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0100 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0872 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
