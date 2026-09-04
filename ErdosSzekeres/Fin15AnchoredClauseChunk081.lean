module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 081. -/

theorem fin15Anchored_clause10368 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10376 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10377 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0183 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1162 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1163 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1163 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1163 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1163 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0184 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1163 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0185 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1164 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10399 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10400 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10401 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0186 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1165 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10407 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10409 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0187 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1166 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10415 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10417 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0188 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1167 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10425 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10426 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10427 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10428 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0189 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1168 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10435 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10436 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0190 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1169 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10444 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0183 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1170 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1171 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1171 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1171 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0184 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1171 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10455 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10457 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0185 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1172 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10464 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10466 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10467 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0186 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1173 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10474 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1174 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1174 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1174 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1174 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1174 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0187 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1174 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10481 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10482 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0188 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1175 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10490 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10491 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10493 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10494 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
