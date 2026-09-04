module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 065. -/

theorem fin15Anchored_clause08320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0110 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0891 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08331 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0892 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0892 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0892 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0892 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0111 Fin15AnchoredAtom0121
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0892 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08336 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08337 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0112 Fin15AnchoredAtom0122
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0893 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08344 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0113 Fin15AnchoredAtom0123
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0894 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08352 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08353 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0114 Fin15AnchoredAtom0124
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0895 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08362 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0106 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0896 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08370 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08371 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0107 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0897 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08379 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08381 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0108 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0898 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08388 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0109 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0899 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08399 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08400 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0110 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0900 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08407 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 Fin15AnchoredAtom0901 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 Fin15AnchoredAtom0901 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 Fin15AnchoredAtom0901 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0111 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0251 Fin15AnchoredAtom0901 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08415 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0112 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0902 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08421 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0113 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0903 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08428 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08429 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0105 Fin15AnchoredAtom0114 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0904 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08438 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0107 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0905 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08446 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08447 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
