module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 111. -/

theorem fin15Anchored_clause14208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14212 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14213 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
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

theorem fin15Anchored_clause14216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0351 Fin15AnchoredAtom0356 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1664 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0354 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1666 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14232 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14233 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0355 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1667 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14239 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14241 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14242 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0352 Fin15AnchoredAtom0356 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1668 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14248 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14249 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0355 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1672 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14260 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14263 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0354 Fin15AnchoredAtom0356 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1673 at hbad
  cases hcolor0 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14271 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0355 Fin15AnchoredAtom0356 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1674 at hbad
  cases hcolor0 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14286 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14287 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0358 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1675 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14293 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14294 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14295 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14296 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1676 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14303 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14304 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14305 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1677 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14316 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14318 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1678 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14326 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14327 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1679 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1680 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1680 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1680 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1680 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
