module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 078. -/

theorem fin15Anchored_clause09984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
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

theorem fin15Anchored_clause09985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
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

theorem fin15Anchored_clause09986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
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

theorem fin15Anchored_clause09987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
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

theorem fin15Anchored_clause09988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09990 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09991 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 Fin15AnchoredAtom1107 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09998 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09999 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 Fin15AnchoredAtom1108 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10007 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom1109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0174 Fin15AnchoredAtom0184
    Fin15AnchoredAtom0239 Fin15AnchoredAtom1109 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10008 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom1109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0174 Fin15AnchoredAtom0184
    Fin15AnchoredAtom0239 Fin15AnchoredAtom1109 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10009 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10010 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10011 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 Fin15AnchoredAtom1110 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10020 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 Fin15AnchoredAtom1111 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10026 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 Fin15AnchoredAtom1112 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10027 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 Fin15AnchoredAtom1112 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 Fin15AnchoredAtom1112 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 Fin15AnchoredAtom1112 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10031 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10032 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10033 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 Fin15AnchoredAtom1113 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10042 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 Fin15AnchoredAtom1114 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10048 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10050 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 Fin15AnchoredAtom1115 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10059 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 Fin15AnchoredAtom1116 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 Fin15AnchoredAtom1117 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom1118 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 Fin15AnchoredAtom1118 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10077 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom1118 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 Fin15AnchoredAtom1118 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10078 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10081 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 Fin15AnchoredAtom1119 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10087 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10088 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10089 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10090 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 Fin15AnchoredAtom1120 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10097 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10098 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10099 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 Fin15AnchoredAtom1121 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10106 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
