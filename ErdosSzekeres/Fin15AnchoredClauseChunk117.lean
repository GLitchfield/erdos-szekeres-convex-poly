module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 117. -/

theorem fin15Anchored_clause14976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14979 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14980 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14981 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0404 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1763 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14990 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14991 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14992 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14993 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0403 Fin15AnchoredAtom0405 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1764 at hbad
  cases hcolor0 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14998 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14999 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0404 Fin15AnchoredAtom0405 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1765 at hbad
  cases hcolor0 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15008 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1766 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15009 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1766 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15010 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1766 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15011 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1766 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1766 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0407 Fin15AnchoredAtom0411
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1766 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15016 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15017 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0408 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1767 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15023 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15025 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15026 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15027 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0409 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1768 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15034 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15035 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15036 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15037 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15038 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0406 Fin15AnchoredAtom0410 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1769 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15046 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15048 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0408 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1770 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15053 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0409 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1771 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15054 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0409 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1771 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0409 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1771 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0409 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1771 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0409 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1771 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0407 Fin15AnchoredAtom0410 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1772 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15059 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15062 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0409 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1773 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15071 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15072 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0408 Fin15AnchoredAtom0410 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1774 at hbad
  cases hcolor0 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15078 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15081 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0409 Fin15AnchoredAtom0410 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1775 at hbad
  cases hcolor0 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15089 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15090 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0412 Fin15AnchoredAtom0415
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1776 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15098 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15099 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15100 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
