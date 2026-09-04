module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 069. -/

theorem fin15Anchored_clause08832 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08833 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08834 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08842 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0123 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0956 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08851 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08852 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0124 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0957 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08857 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0118 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0958 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08866 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08867 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08868 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0119 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0959 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08874 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08875 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08876 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08877 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08879 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0120 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0960 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08884 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08885 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08886 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08888 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0121 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0961 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08896 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0122 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0962 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08903 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08904 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08906 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08907 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0123 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0963 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08913 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08914 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08915 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0117 Fin15AnchoredAtom0124 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0964 at hbad
  cases hcolor0 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08923 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08924 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0119 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0965 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08931 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08932 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08933 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0120 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0966 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08943 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08945 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0122 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0968 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08951 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08952 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08953 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08954 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0123 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0969 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
