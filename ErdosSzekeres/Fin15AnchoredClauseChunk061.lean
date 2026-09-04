module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 061. -/

theorem fin15Anchored_clause07808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0820 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0820 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0820 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0820 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07813 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07814 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0094 Fin15AnchoredAtom0105
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0821 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07820 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07823 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0095 Fin15AnchoredAtom0106
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0822 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0096 Fin15AnchoredAtom0107
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0823 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 Fin15AnchoredAtom0824 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07837 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0097 Fin15AnchoredAtom0108
    Fin15AnchoredAtom0174 Fin15AnchoredAtom0824 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07838 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0098 Fin15AnchoredAtom0109
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0825 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07846 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07851 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0099 Fin15AnchoredAtom0110
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0826 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07857 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 Fin15AnchoredAtom0827 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 Fin15AnchoredAtom0827 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0100 Fin15AnchoredAtom0111
    Fin15AnchoredAtom0177 Fin15AnchoredAtom0827 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07861 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07862 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07863 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0101 Fin15AnchoredAtom0112
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0828 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07869 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07870 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0102 Fin15AnchoredAtom0113
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0829 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07879 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0103 Fin15AnchoredAtom0114
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0830 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07888 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07890 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07891 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0094 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0831 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07900 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07901 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0095 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0832 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07908 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07909 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07910 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0096 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0833 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07918 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0834 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0834 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0834 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0834 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0834 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0097 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0834 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07924 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0098 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0835 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0093 Fin15AnchoredAtom0099 Fin15AnchoredAtom0120
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0836 at hbad
  cases hcolor0 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
