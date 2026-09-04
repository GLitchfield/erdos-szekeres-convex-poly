module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 060. -/

theorem fin15Anchored_clause07680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0062 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0388 Fin15AnchoredAtom0752 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0062 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0388 Fin15AnchoredAtom0752 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0063 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0389 Fin15AnchoredAtom0753 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0063 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0389 Fin15AnchoredAtom0753 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0060 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0390 Fin15AnchoredAtom0754 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07685 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0060 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0390 Fin15AnchoredAtom0754 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07686 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0061 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0391 Fin15AnchoredAtom0755 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07687 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0061 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0391 Fin15AnchoredAtom0755 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0062 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0392 Fin15AnchoredAtom0756 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07689 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0062 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0392 Fin15AnchoredAtom0756 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07690 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0063 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0393 Fin15AnchoredAtom0757 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 Fin15AnchoredAtom0063 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0393 Fin15AnchoredAtom0757 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 Fin15AnchoredAtom0061 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0394 Fin15AnchoredAtom0758 at hbad
  cases hcolor0 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 Fin15AnchoredAtom0061 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0394 Fin15AnchoredAtom0758 at hbad
  cases hcolor0 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 Fin15AnchoredAtom0062 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0395 Fin15AnchoredAtom0759 at hbad
  cases hcolor0 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07695 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 Fin15AnchoredAtom0062 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0395 Fin15AnchoredAtom0759 at hbad
  cases hcolor0 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07696 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0760 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 Fin15AnchoredAtom0063 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0396 Fin15AnchoredAtom0760 at hbad
  cases hcolor0 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0760 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 Fin15AnchoredAtom0063 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0396 Fin15AnchoredAtom0760 at hbad
  cases hcolor0 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07698 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0061 Fin15AnchoredAtom0062 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0397 Fin15AnchoredAtom0761 at hbad
  cases hcolor0 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0061 Fin15AnchoredAtom0062 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0397 Fin15AnchoredAtom0761 at hbad
  cases hcolor0 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0061 Fin15AnchoredAtom0063 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0398 Fin15AnchoredAtom0762 at hbad
  cases hcolor0 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07701 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0061 Fin15AnchoredAtom0063 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0398 Fin15AnchoredAtom0762 at hbad
  cases hcolor0 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07702 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0062 Fin15AnchoredAtom0063 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0399 Fin15AnchoredAtom0763 at hbad
  cases hcolor0 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0062 Fin15AnchoredAtom0063 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0399 Fin15AnchoredAtom0763 at hbad
  cases hcolor0 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07704 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0065 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0400 Fin15AnchoredAtom0764 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0065 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0400 Fin15AnchoredAtom0764 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07706 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0066 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0401 Fin15AnchoredAtom0765 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0066 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0401 Fin15AnchoredAtom0765 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0068 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0403 Fin15AnchoredAtom0767 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07709 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0068 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0403 Fin15AnchoredAtom0767 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07710 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0069 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0404 Fin15AnchoredAtom0768 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07711 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0069 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0404 Fin15AnchoredAtom0768 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07712 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0070 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0405 Fin15AnchoredAtom0769 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 Fin15AnchoredAtom0070 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0405 Fin15AnchoredAtom0769 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0066 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0406 Fin15AnchoredAtom0770 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07715 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0066 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0406 Fin15AnchoredAtom0770 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0067 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0407 Fin15AnchoredAtom0771 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07717 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0067 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0407 Fin15AnchoredAtom0771 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0068 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0408 Fin15AnchoredAtom0772 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0068 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0408 Fin15AnchoredAtom0772 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07720 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0069 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0409 Fin15AnchoredAtom0773 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07721 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0069 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0409 Fin15AnchoredAtom0773 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0070 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0410 Fin15AnchoredAtom0774 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07723 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 Fin15AnchoredAtom0070 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0410 Fin15AnchoredAtom0774 at hbad
  cases hcolor0 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07724 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0067 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0411 Fin15AnchoredAtom0775 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0067 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0411 Fin15AnchoredAtom0775 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0068 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0412 Fin15AnchoredAtom0776 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07727 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0068 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0412 Fin15AnchoredAtom0776 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07728 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0069 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0413 Fin15AnchoredAtom0777 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07729 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0069 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0413 Fin15AnchoredAtom0777 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0070 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0414 Fin15AnchoredAtom0778 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 Fin15AnchoredAtom0070 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0414 Fin15AnchoredAtom0778 at hbad
  cases hcolor0 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07732 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 Fin15AnchoredAtom0068 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0415 Fin15AnchoredAtom0779 at hbad
  cases hcolor0 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07733 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 Fin15AnchoredAtom0068 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0415 Fin15AnchoredAtom0779 at hbad
  cases hcolor0 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07734 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 Fin15AnchoredAtom0069 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0416 Fin15AnchoredAtom0780 at hbad
  cases hcolor0 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07735 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 Fin15AnchoredAtom0069 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0416 Fin15AnchoredAtom0780 at hbad
  cases hcolor0 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 Fin15AnchoredAtom0070 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0417 Fin15AnchoredAtom0781 at hbad
  cases hcolor0 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 Fin15AnchoredAtom0070 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0417 Fin15AnchoredAtom0781 at hbad
  cases hcolor0 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07738 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0068 Fin15AnchoredAtom0069 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0418 Fin15AnchoredAtom0782 at hbad
  cases hcolor0 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0068 Fin15AnchoredAtom0069 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0418 Fin15AnchoredAtom0782 at hbad
  cases hcolor0 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0068 Fin15AnchoredAtom0070 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0419 Fin15AnchoredAtom0783 at hbad
  cases hcolor0 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0068 Fin15AnchoredAtom0070 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0419 Fin15AnchoredAtom0783 at hbad
  cases hcolor0 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0069 Fin15AnchoredAtom0070 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0420 Fin15AnchoredAtom0784 at hbad
  cases hcolor0 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07743 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0069 Fin15AnchoredAtom0070 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0420 Fin15AnchoredAtom0784 at hbad
  cases hcolor0 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07744 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0072 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0421 Fin15AnchoredAtom0785 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07745 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0072 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0421 Fin15AnchoredAtom0785 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07746 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0074 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0423 Fin15AnchoredAtom0787 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0074 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0423 Fin15AnchoredAtom0787 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0075 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0424 Fin15AnchoredAtom0788 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0075 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0424 Fin15AnchoredAtom0788 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0076 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0425 Fin15AnchoredAtom0789 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07751 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 Fin15AnchoredAtom0076 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0425 Fin15AnchoredAtom0789 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07752 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 Fin15AnchoredAtom0074 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0427 Fin15AnchoredAtom0791 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07753 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 Fin15AnchoredAtom0074 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0427 Fin15AnchoredAtom0791 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07754 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 Fin15AnchoredAtom0075 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0428 Fin15AnchoredAtom0792 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 Fin15AnchoredAtom0075 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0428 Fin15AnchoredAtom0792 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 Fin15AnchoredAtom0076 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0429 Fin15AnchoredAtom0793 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 Fin15AnchoredAtom0076 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0429 Fin15AnchoredAtom0793 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07758 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0074 Fin15AnchoredAtom0075 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0433 Fin15AnchoredAtom0797 at hbad
  cases hcolor0 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0074 Fin15AnchoredAtom0075 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0433 Fin15AnchoredAtom0797 at hbad
  cases hcolor0 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0074 Fin15AnchoredAtom0076 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0434 Fin15AnchoredAtom0798 at hbad
  cases hcolor0 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0074 Fin15AnchoredAtom0076 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0434 Fin15AnchoredAtom0798 at hbad
  cases hcolor0 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0075 Fin15AnchoredAtom0076 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0435 Fin15AnchoredAtom0799 at hbad
  cases hcolor0 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07763 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0075 Fin15AnchoredAtom0076 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0435 Fin15AnchoredAtom0799 at hbad
  cases hcolor0 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07764 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0078 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0436 Fin15AnchoredAtom0800 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07765 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0078 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0436 Fin15AnchoredAtom0800 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0079 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0437 Fin15AnchoredAtom0801 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07767 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0079 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0437 Fin15AnchoredAtom0801 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0080 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0438 Fin15AnchoredAtom0802 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0080 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0438 Fin15AnchoredAtom0802 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07770 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0081 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0439 Fin15AnchoredAtom0803 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 Fin15AnchoredAtom0081 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0439 Fin15AnchoredAtom0803 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 Fin15AnchoredAtom0079 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0440 Fin15AnchoredAtom0804 at hbad
  cases hcolor0 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07773 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 Fin15AnchoredAtom0079 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0440 Fin15AnchoredAtom0804 at hbad
  cases hcolor0 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07774 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 Fin15AnchoredAtom0080 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0441 Fin15AnchoredAtom0805 at hbad
  cases hcolor0 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 Fin15AnchoredAtom0080 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0441 Fin15AnchoredAtom0805 at hbad
  cases hcolor0 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07776 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 Fin15AnchoredAtom0081 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0442 Fin15AnchoredAtom0806 at hbad
  cases hcolor0 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 Fin15AnchoredAtom0081 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0442 Fin15AnchoredAtom0806 at hbad
  cases hcolor0 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0079 Fin15AnchoredAtom0080 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0443 Fin15AnchoredAtom0807 at hbad
  cases hcolor0 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07779 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0079 Fin15AnchoredAtom0080 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0443 Fin15AnchoredAtom0807 at hbad
  cases hcolor0 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07780 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0079 Fin15AnchoredAtom0081 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0444 Fin15AnchoredAtom0808 at hbad
  cases hcolor0 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0079 Fin15AnchoredAtom0081 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0444 Fin15AnchoredAtom0808 at hbad
  cases hcolor0 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0080 Fin15AnchoredAtom0081 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0445 Fin15AnchoredAtom0809 at hbad
  cases hcolor0 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07783 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0080 Fin15AnchoredAtom0081 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0445 Fin15AnchoredAtom0809 at hbad
  cases hcolor0 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07784 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 Fin15AnchoredAtom0083 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0446 Fin15AnchoredAtom0810 at hbad
  cases hcolor0 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07785 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 Fin15AnchoredAtom0083 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0446 Fin15AnchoredAtom0810 at hbad
  cases hcolor0 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 Fin15AnchoredAtom0084 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0447 Fin15AnchoredAtom0811 at hbad
  cases hcolor0 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07787 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 Fin15AnchoredAtom0084 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0447 Fin15AnchoredAtom0811 at hbad
  cases hcolor0 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 Fin15AnchoredAtom0085 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0448 Fin15AnchoredAtom0812 at hbad
  cases hcolor0 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 Fin15AnchoredAtom0085 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0448 Fin15AnchoredAtom0812 at hbad
  cases hcolor0 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0083 Fin15AnchoredAtom0084 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0449 Fin15AnchoredAtom0813 at hbad
  cases hcolor0 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0083 Fin15AnchoredAtom0084 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0449 Fin15AnchoredAtom0813 at hbad
  cases hcolor0 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07792 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0083 Fin15AnchoredAtom0085 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0450 Fin15AnchoredAtom0814 at hbad
  cases hcolor0 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07793 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0083 Fin15AnchoredAtom0085 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0450 Fin15AnchoredAtom0814 at hbad
  cases hcolor0 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0084 Fin15AnchoredAtom0085 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0451 Fin15AnchoredAtom0815 at hbad
  cases hcolor0 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07795 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0084 Fin15AnchoredAtom0085 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0451 Fin15AnchoredAtom0815 at hbad
  cases hcolor0 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0086 Fin15AnchoredAtom0087 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0452 Fin15AnchoredAtom0816 at hbad
  cases hcolor0 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0086 Fin15AnchoredAtom0087 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0452 Fin15AnchoredAtom0816 at hbad
  cases hcolor0 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0086 Fin15AnchoredAtom0088 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0453 Fin15AnchoredAtom0817 at hbad
  cases hcolor0 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0086 Fin15AnchoredAtom0088 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0453 Fin15AnchoredAtom0817 at hbad
  cases hcolor0 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0087 Fin15AnchoredAtom0088 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0454 Fin15AnchoredAtom0818 at hbad
  cases hcolor0 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07801 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0087 Fin15AnchoredAtom0088 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0454 Fin15AnchoredAtom0818 at hbad
  cases hcolor0 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07802 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0089 Fin15AnchoredAtom0090 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0455 Fin15AnchoredAtom0819 at hbad
  cases hcolor0 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0089 Fin15AnchoredAtom0090 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0455 Fin15AnchoredAtom0819 at hbad
  cases hcolor0 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07804 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
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

theorem fin15Anchored_clause07805 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0820 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
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

theorem fin15Anchored_clause07807 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0092 Fin15AnchoredAtom0093 Fin15AnchoredAtom0104
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0820 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
