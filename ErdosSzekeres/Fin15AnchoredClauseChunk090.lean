module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 090. -/

theorem fin15Anchored_clause11520 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11528 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11531 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 Fin15AnchoredAtom1337 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11537 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 Fin15AnchoredAtom1338 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11547 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1339 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1339 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom1339 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 Fin15AnchoredAtom1339 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11550 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 Fin15AnchoredAtom1340 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11559 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11560 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11561 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1341 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11568 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1342 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11576 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11577 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11579 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1343 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11585 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11589 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1344 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11600 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1345 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1346 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1346 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1346 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11609 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11610 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11611 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11612 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1347 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1348 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11627 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1349 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11635 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11636 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1350 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11647 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
