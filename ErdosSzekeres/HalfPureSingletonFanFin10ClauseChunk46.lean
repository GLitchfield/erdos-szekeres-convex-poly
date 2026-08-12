module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 46. -/

theorem halfPureSingletonFanFin10_clause07593 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0416 χ ∧
      ¬HalfPureSingletonFanFin10Atom0168 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0168 HalfPureSingletonFanFin10Atom0416 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0677] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07594 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0416 χ ∧
      ¬HalfPureSingletonFanFin10Atom0199 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0199 HalfPureSingletonFanFin10Atom0416 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0677] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07595 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0416 χ ∧
      ¬HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0290 HalfPureSingletonFanFin10Atom0416 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0677] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07597 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0668 χ ∧
      ¬HalfPureSingletonFanFin10Atom0416 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0416 HalfPureSingletonFanFin10Atom0668 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0677, halfPureSingletonFanFin10_cupSet_iff_mask0677] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07609 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0920 χ ∧
      ¬HalfPureSingletonFanFin10Atom0416 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0416 HalfPureSingletonFanFin10Atom0920 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0677, halfPureSingletonFanFin10_capSet_iff_mask0677] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07621 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0417 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0417 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07622 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0417 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0417 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07623 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0417 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0169 HalfPureSingletonFanFin10Atom0417 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07624 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0417 χ ∧
      ¬HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0417 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07625 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0417 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0417 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07627 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0669 χ ∧
      ¬HalfPureSingletonFanFin10Atom0417 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0417 HalfPureSingletonFanFin10Atom0669 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805, halfPureSingletonFanFin10_cupSet_iff_mask0805] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07628 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0669 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0669 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805, halfPureSingletonFanFin10_cupSet_iff_mask0805] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07639 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0921 χ ∧
      ¬HalfPureSingletonFanFin10Atom0417 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0417 HalfPureSingletonFanFin10Atom0921 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0805, halfPureSingletonFanFin10_capSet_iff_mask0805] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07651 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0418 χ ∧
      ¬HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0164 HalfPureSingletonFanFin10Atom0418 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07652 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0418 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0165 HalfPureSingletonFanFin10Atom0418 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07653 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0418 χ ∧
      ¬HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0167 HalfPureSingletonFanFin10Atom0418 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07654 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0418 χ ∧
      ¬HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0201 HalfPureSingletonFanFin10Atom0418 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07655 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0418 χ ∧
      ¬HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0418 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07657 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0670 χ ∧
      ¬HalfPureSingletonFanFin10Atom0418 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0418 HalfPureSingletonFanFin10Atom0670 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453, halfPureSingletonFanFin10_cupSet_iff_mask0453] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07658 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0670 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0013 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0013
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0031
    HalfPureSingletonFanFin10Atom0032 HalfPureSingletonFanFin10Atom0034
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0083 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0670 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453, halfPureSingletonFanFin10_cupSet_iff_mask0453] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07669 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0922 χ ∧
      ¬HalfPureSingletonFanFin10Atom0418 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0418 HalfPureSingletonFanFin10Atom0922 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0453, halfPureSingletonFanFin10_capSet_iff_mask0453] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07681 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0419 χ ∧
      ¬HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0164 HalfPureSingletonFanFin10Atom0419 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07682 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0419 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0419 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07683 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0419 χ ∧
      ¬HalfPureSingletonFanFin10Atom0168 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0168 HalfPureSingletonFanFin10Atom0419 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07684 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0419 χ ∧
      ¬HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0202 HalfPureSingletonFanFin10Atom0419 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07685 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0419 χ ∧
      ¬HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0293 HalfPureSingletonFanFin10Atom0419 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07687 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0671 χ ∧
      ¬HalfPureSingletonFanFin10Atom0419 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0419 HalfPureSingletonFanFin10Atom0671 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709, halfPureSingletonFanFin10_cupSet_iff_mask0709] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07699 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0923 χ ∧
      ¬HalfPureSingletonFanFin10Atom0419 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0419 HalfPureSingletonFanFin10Atom0923 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0709, halfPureSingletonFanFin10_capSet_iff_mask0709] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07711 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0420 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0165 HalfPureSingletonFanFin10Atom0420 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07712 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0420 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0420 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07713 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0420 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0169 HalfPureSingletonFanFin10Atom0420 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07714 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0420 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0203 HalfPureSingletonFanFin10Atom0420 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837] at hbad
  tauto

end ErdosSzekeres

end
