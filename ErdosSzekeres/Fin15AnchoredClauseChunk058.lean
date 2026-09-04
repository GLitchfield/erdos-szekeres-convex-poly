module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 058. -/

theorem fin15Anchored_clause07424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0030 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0620 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07425 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0030 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0620 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07426 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0031 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0621 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07427 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0031 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0621 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07428 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0032 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0622 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07429 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0032 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0622 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0033 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0259 Fin15AnchoredAtom0623 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0033 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0259 Fin15AnchoredAtom0623 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0034 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0624 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07433 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0034 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0624 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0035 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0625 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07435 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0035 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0625 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07436 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0036 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0626 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0036 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0626 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07438 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0030 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0627 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0030 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0627 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0031 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0628 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07441 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0031 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0628 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0032 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0629 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0032 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0629 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07444 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0033 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0266 Fin15AnchoredAtom0630 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0033 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0266 Fin15AnchoredAtom0630 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07446 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0034 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0631 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07447 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0034 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0631 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0035 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0632 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0035 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0632 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0036 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0633 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0029 Fin15AnchoredAtom0036 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0633 at hbad
  cases hcolor0 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0031 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0634 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0031 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0634 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07454 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0032 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0635 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07455 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0032 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0635 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0034 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0637 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07457 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0034 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0637 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0035 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0638 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0035 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0638 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07460 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0036 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0639 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07461 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0030 Fin15AnchoredAtom0036 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0639 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0032 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0640 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07463 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0032 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0640 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07464 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0033 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0641 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0033 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0641 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07466 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0034 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0642 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07467 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0034 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0642 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0035 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0643 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07469 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0035 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0643 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07470 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0036 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0644 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07471 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0031 Fin15AnchoredAtom0036 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0644 at hbad
  cases hcolor0 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0033 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0281 Fin15AnchoredAtom0645 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0033 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0281 Fin15AnchoredAtom0645 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07474 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0034 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0646 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07475 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0034 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0646 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07476 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0035 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0647 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0035 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0647 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0036 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0648 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07479 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0032 Fin15AnchoredAtom0036 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0648 at hbad
  cases hcolor0 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0033 Fin15AnchoredAtom0034 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0649 at hbad
  cases hcolor0 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07481 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0033 Fin15AnchoredAtom0034 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0649 at hbad
  cases hcolor0 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07482 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0033 Fin15AnchoredAtom0035 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0286 Fin15AnchoredAtom0650 at hbad
  cases hcolor0 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0033 Fin15AnchoredAtom0035 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0286 Fin15AnchoredAtom0650 at hbad
  cases hcolor0 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0033 Fin15AnchoredAtom0036 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0287 Fin15AnchoredAtom0651 at hbad
  cases hcolor0 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0033 Fin15AnchoredAtom0036 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0287 Fin15AnchoredAtom0651 at hbad
  cases hcolor0 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0034 Fin15AnchoredAtom0035 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0652 at hbad
  cases hcolor0 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0034 Fin15AnchoredAtom0035 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0652 at hbad
  cases hcolor0 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0034 Fin15AnchoredAtom0036 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0653 at hbad
  cases hcolor0 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0034 Fin15AnchoredAtom0036 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0653 at hbad
  cases hcolor0 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07490 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0035 Fin15AnchoredAtom0036 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0654 at hbad
  cases hcolor0 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07491 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0035 Fin15AnchoredAtom0036 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0654 at hbad
  cases hcolor0 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0038 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0655 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07493 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0038 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0655 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07494 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0039 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0656 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0039 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0656 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0040 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0657 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07497 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0040 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0657 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0041 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0658 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07499 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0041 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0658 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07500 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0042 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0659 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0042 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0659 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07502 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0043 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0296 Fin15AnchoredAtom0660 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07503 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0043 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0296 Fin15AnchoredAtom0660 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07504 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0044 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0661 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0044 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0661 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07506 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0045 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0662 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07507 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0045 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0662 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07508 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0046 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0663 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0037 Fin15AnchoredAtom0046 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0663 at hbad
  cases hcolor0 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07510 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0039 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0664 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0039 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0664 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0040 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0665 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07513 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0040 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0665 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07514 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0041 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0666 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0041 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0666 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07516 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0042 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0667 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07517 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0042 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0667 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0043 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0304 Fin15AnchoredAtom0668 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07519 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0043 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0304 Fin15AnchoredAtom0668 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07520 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0044 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0669 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0044 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0669 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0045 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0670 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0045 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0306 Fin15AnchoredAtom0670 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0046 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0671 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07525 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 Fin15AnchoredAtom0046 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0307 Fin15AnchoredAtom0671 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07526 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0040 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0672 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07527 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0040 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0308 Fin15AnchoredAtom0672 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07528 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0041 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0673 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0041 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0309 Fin15AnchoredAtom0673 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0042 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0674 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07531 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0042 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0310 Fin15AnchoredAtom0674 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07532 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0043 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0675 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0043 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0311 Fin15AnchoredAtom0675 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07534 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0044 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0676 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0044 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0312 Fin15AnchoredAtom0676 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0045 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0677 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07537 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0045 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0313 Fin15AnchoredAtom0677 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0046 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0678 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 Fin15AnchoredAtom0046 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0314 Fin15AnchoredAtom0678 at hbad
  cases hcolor0 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0041 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0679 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0041 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0315 Fin15AnchoredAtom0679 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0042 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0680 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07543 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0042 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0316 Fin15AnchoredAtom0680 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07544 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0044 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0682 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07545 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0044 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0318 Fin15AnchoredAtom0682 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07546 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0045 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0683 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07547 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0045 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0319 Fin15AnchoredAtom0683 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07548 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0046 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0684 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 Fin15AnchoredAtom0046 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0684 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07550 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0042 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0685 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0042 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0685 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
