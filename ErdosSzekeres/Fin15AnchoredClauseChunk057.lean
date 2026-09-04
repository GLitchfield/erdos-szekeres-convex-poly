module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 057. -/

theorem fin15Anchored_clause07296 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0025 Fin15AnchoredAtom0046
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0554 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0017 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0555 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0017 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0191 Fin15AnchoredAtom0555 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0018 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0556 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07300 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0018 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0192 Fin15AnchoredAtom0556 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0557 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0019 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0193 Fin15AnchoredAtom0557 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0557 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0019 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0193 Fin15AnchoredAtom0557 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07303 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0020 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0558 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07304 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0020 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0194 Fin15AnchoredAtom0558 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07305 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0021 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0559 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0021 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0195 Fin15AnchoredAtom0559 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0022 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0560 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0022 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0196 Fin15AnchoredAtom0560 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07309 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0023 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0561 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07310 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0023 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0197 Fin15AnchoredAtom0561 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07311 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0024 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0562 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07312 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0024 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0198 Fin15AnchoredAtom0562 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0025 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0563 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0016 Fin15AnchoredAtom0025 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0199 Fin15AnchoredAtom0563 at hbad
  cases hcolor0 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0018 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0564 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07316 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0018 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0200 Fin15AnchoredAtom0564 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0019 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0201 Fin15AnchoredAtom0565 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07318 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0019 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0201 Fin15AnchoredAtom0565 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07319 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0020 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0566 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07320 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0020 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0202 Fin15AnchoredAtom0566 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07321 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0021 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0567 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0021 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0203 Fin15AnchoredAtom0567 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0022 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0568 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0022 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0204 Fin15AnchoredAtom0568 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0023 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0569 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07326 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0023 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0205 Fin15AnchoredAtom0569 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07327 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0024 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0570 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0024 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0206 Fin15AnchoredAtom0570 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07329 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0025 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0571 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07330 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0017 Fin15AnchoredAtom0025 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0207 Fin15AnchoredAtom0571 at hbad
  cases hcolor0 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07331 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0019 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0208 Fin15AnchoredAtom0572 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0019 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0208 Fin15AnchoredAtom0572 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0020 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0573 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0020 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0209 Fin15AnchoredAtom0573 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07335 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0021 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0574 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07336 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0021 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0210 Fin15AnchoredAtom0574 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07337 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0022 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0211 Fin15AnchoredAtom0575 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0022 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0211 Fin15AnchoredAtom0575 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0023 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0576 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0023 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0212 Fin15AnchoredAtom0576 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07341 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0024 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0577 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07342 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0024 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0213 Fin15AnchoredAtom0577 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07343 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0025 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0578 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07344 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0018 Fin15AnchoredAtom0025 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0214 Fin15AnchoredAtom0578 at hbad
  cases hcolor0 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0020 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0215 Fin15AnchoredAtom0579 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0020 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0215 Fin15AnchoredAtom0579 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0021 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0580 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0021 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0216 Fin15AnchoredAtom0580 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0023 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0218 Fin15AnchoredAtom0582 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07350 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0023 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0218 Fin15AnchoredAtom0582 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0024 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0219 Fin15AnchoredAtom0583 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07352 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0025 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0220 Fin15AnchoredAtom0584 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07353 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0019 Fin15AnchoredAtom0025 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0220 Fin15AnchoredAtom0584 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0021 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0585 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0021 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0221 Fin15AnchoredAtom0585 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0022 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0586 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0022 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0222 Fin15AnchoredAtom0586 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0023 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0587 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07359 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0023 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0587 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0024 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0588 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0024 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0588 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07362 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0025 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0589 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0020 Fin15AnchoredAtom0025 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0589 at hbad
  cases hcolor0 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07364 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0022 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0226 Fin15AnchoredAtom0590 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07365 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0022 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0226 Fin15AnchoredAtom0590 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0023 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0591 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07367 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0023 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0591 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07368 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0024 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0592 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0024 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0592 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07370 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0025 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0593 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07371 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0021 Fin15AnchoredAtom0025 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0593 at hbad
  cases hcolor0 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0022 Fin15AnchoredAtom0023 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0230 Fin15AnchoredAtom0594 at hbad
  cases hcolor0 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0022 Fin15AnchoredAtom0023 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0230 Fin15AnchoredAtom0594 at hbad
  cases hcolor0 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0022 Fin15AnchoredAtom0024 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0231 Fin15AnchoredAtom0595 at hbad
  cases hcolor0 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0022 Fin15AnchoredAtom0024 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0231 Fin15AnchoredAtom0595 at hbad
  cases hcolor0 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07376 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0022 Fin15AnchoredAtom0025 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0232 Fin15AnchoredAtom0596 at hbad
  cases hcolor0 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07377 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0022 Fin15AnchoredAtom0025 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0232 Fin15AnchoredAtom0596 at hbad
  cases hcolor0 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0023 Fin15AnchoredAtom0024 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0597 at hbad
  cases hcolor0 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07379 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0023 Fin15AnchoredAtom0024 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0597 at hbad
  cases hcolor0 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0023 Fin15AnchoredAtom0025 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0598 at hbad
  cases hcolor0 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07381 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0023 Fin15AnchoredAtom0025 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0598 at hbad
  cases hcolor0 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07382 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0024 Fin15AnchoredAtom0025 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0599 at hbad
  cases hcolor0 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0024 Fin15AnchoredAtom0025 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0599 at hbad
  cases hcolor0 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0027 Fin15AnchoredAtom0037
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0600 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0027 Fin15AnchoredAtom0037
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0600 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0028 Fin15AnchoredAtom0038
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0601 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07387 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0028 Fin15AnchoredAtom0038
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0601 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07388 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0029 Fin15AnchoredAtom0039
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0602 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0029 Fin15AnchoredAtom0039
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0602 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0030 Fin15AnchoredAtom0040
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0603 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0030 Fin15AnchoredAtom0040
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0603 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0031 Fin15AnchoredAtom0041
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0604 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07393 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0031 Fin15AnchoredAtom0041
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0604 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07394 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0032 Fin15AnchoredAtom0042
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0605 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0032 Fin15AnchoredAtom0042
    Fin15AnchoredAtom0241 Fin15AnchoredAtom0605 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07396 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0033 Fin15AnchoredAtom0043
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0606 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0033 Fin15AnchoredAtom0043
    Fin15AnchoredAtom0242 Fin15AnchoredAtom0606 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0034 Fin15AnchoredAtom0044
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0607 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07399 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0034 Fin15AnchoredAtom0044
    Fin15AnchoredAtom0243 Fin15AnchoredAtom0607 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07400 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0035 Fin15AnchoredAtom0045
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0608 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07401 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0035 Fin15AnchoredAtom0045
    Fin15AnchoredAtom0244 Fin15AnchoredAtom0608 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0036 Fin15AnchoredAtom0046
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0609 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07403 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0026 Fin15AnchoredAtom0036 Fin15AnchoredAtom0046
    Fin15AnchoredAtom0245 Fin15AnchoredAtom0609 at hbad
  cases hcolor0 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0028 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0610 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0028 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0246 Fin15AnchoredAtom0610 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07406 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0029 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0611 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07407 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0029 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0247 Fin15AnchoredAtom0611 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0030 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0612 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07409 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0030 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0248 Fin15AnchoredAtom0612 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07410 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0031 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0613 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0031 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0249 Fin15AnchoredAtom0613 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0032 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0614 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0032 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0250 Fin15AnchoredAtom0614 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0033 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0251 Fin15AnchoredAtom0615 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07415 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0033 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0251 Fin15AnchoredAtom0615 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0034 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0616 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07417 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0034 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0252 Fin15AnchoredAtom0616 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0035 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0617 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0035 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0253 Fin15AnchoredAtom0617 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0036 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0618 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07421 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0027 Fin15AnchoredAtom0036 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0254 Fin15AnchoredAtom0618 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0029 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0619 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0028 Fin15AnchoredAtom0029 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0255 Fin15AnchoredAtom0619 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
