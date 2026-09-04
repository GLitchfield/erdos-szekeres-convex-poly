module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 095. -/

theorem fin15Anchored_clause12160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12163 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1415 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1417 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12179 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1418 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12186 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12187 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12189 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1419 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12194 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12198 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1420 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1421 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1421 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1421 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1421 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1422 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12215 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1423 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12225 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12226 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1424 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1425 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12236 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1425 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1425 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1425 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1425 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1425 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12241 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12242 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12243 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1426 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12255 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1427 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12263 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1428 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1429 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1429 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1429 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1429 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1430 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12277 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1430 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12278 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1430 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1430 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
