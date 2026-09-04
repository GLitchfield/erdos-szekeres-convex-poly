module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 110. -/

theorem fin15Anchored_clause14080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14081 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14083 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1648 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14090 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1649 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14099 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14100 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1650 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14109 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14110 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1651 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14118 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14120 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1652 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14127 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14128 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14129 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1653 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14138 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14139 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14140 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1654 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14148 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0349 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1655 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0350 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1656 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0350 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1656 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14156 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0349 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1657 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14163 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0348 Fin15AnchoredAtom0350 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1658 at hbad
  cases hcolor0 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14173 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14175 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14176 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0349 Fin15AnchoredAtom0350 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1659 at hbad
  cases hcolor0 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0352 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1660 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14194 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0354 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1662 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14201 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0355 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1663 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
