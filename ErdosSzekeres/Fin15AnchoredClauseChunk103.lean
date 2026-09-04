module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 103. -/

theorem fin15Anchored_clause13184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13186 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13187 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0304 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1541 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13194 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0305 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1542 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13206 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0306 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1543 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0307 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1544 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0304 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1545 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13239 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0305 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1546 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13248 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13249 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0306 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1547 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13256 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13257 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13258 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13260 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0303 Fin15AnchoredAtom0307 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1548 at hbad
  cases hcolor0 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13268 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13269 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13271 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0305 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1549 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13277 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13278 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0306 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1550 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1551 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1551 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1551 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0304 Fin15AnchoredAtom0307 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1551 at hbad
  cases hcolor0 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13289 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13293 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0306 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1552 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13300 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0305 Fin15AnchoredAtom0307 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1553 at hbad
  cases hcolor0 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13309 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13310 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13311 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
