module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 041. -/

theorem fin15Anchored_clause05248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05256 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05257 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05258 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05259 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05260 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05261 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05262 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05263 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05264 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05265 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05266 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05267 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05268 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05269 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05270 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05271 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05272 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05273 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05274 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05275 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05276 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05277 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05278 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05279 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05280 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05281 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05282 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05283 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05284 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05285 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05286 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05287 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05288 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05289 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05290 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05291 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05292 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05293 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05294 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05295 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05296 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05297 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05298 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05299 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05300 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05301 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05302 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05303 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05304 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05305 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05306 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05307 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05308 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05309 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05310 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05311 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05312 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05313 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05314 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05315 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05316 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05317 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05318 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05319 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05320 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05321 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05322 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05323 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05324 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05325 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05326 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05327 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05328 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05329 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05330 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05331 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05332 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05333 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05334 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05335 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05336 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05337 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05338 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05339 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05340 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05341 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05342 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05343 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05344 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05345 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05346 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05347 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05348 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05349 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05350 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05351 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05352 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05353 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05354 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05355 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05356 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05357 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05358 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05359 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05360 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05361 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05362 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05363 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05364 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05365 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05366 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05367 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05368 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05369 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05370 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05371 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05372 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05373 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05374 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05375 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
