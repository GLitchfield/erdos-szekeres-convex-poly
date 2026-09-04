module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 071. -/

theorem fin15Anchored_clause09088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0988 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09100 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0989 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0990 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0990 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0990 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0990 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0990 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0990 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09120 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0991 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09129 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0132 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0992 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09139 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09140 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0133 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0993 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09150 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0127 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0994 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09157 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09158 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09159 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0128 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0995 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09167 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0129 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0996 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0997 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 Fin15AnchoredAtom0997 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0997 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0130 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0347 Fin15AnchoredAtom0997 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09179 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09181 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0131 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0998 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09189 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0132 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0999 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09201 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0126 Fin15AnchoredAtom0133 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1000 at hbad
  cases hcolor0 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09212 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09213 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
