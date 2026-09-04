module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 020. -/

theorem fin15Anchored_clause02560 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02561 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02562 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02563 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02564 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02565 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02566 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02567 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02568 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02569 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02570 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02571 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02572 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02573 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02574 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02575 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02576 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02577 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02578 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02579 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02580 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02581 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02582 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02583 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02584 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02585 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02586 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02587 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02588 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02589 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02590 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02591 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02592 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02593 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02594 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02595 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02596 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02597 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02598 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02599 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02600 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02601 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02602 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02603 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02604 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02605 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02606 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02607 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02608 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02609 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02610 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02611 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02612 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02613 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02614 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02615 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02616 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02617 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02618 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02619 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02620 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02621 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02622 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02623 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02624 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02625 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02626 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02627 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02628 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02629 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02630 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02631 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02632 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02633 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02634 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02635 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02636 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02637 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02638 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02639 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02640 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02641 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02642 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02643 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02644 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02645 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02646 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02647 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02648 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02649 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02650 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02651 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02652 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02653 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02654 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02655 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02656 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02657 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02658 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02659 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02660 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02661 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02662 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02663 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02664 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02665 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02666 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02667 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02668 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02669 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02670 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02671 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02672 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02673 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02674 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02675 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02676 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02677 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02678 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02679 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02680 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02681 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02682 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02683 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02684 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02685 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02686 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02687 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
