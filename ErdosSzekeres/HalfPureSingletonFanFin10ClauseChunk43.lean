module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 43. -/

theorem halfPureSingletonFanFin10_clause06937 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0646 χ ∧
      ¬HalfPureSingletonFanFin10Atom0394 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0394 HalfPureSingletonFanFin10Atom0646 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301, halfPureSingletonFanFin10_cupSet_iff_mask0301] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06938 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0646 χ ∧
      HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0017
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0646 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301, halfPureSingletonFanFin10_cupSet_iff_mask0301] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06949 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0898 χ ∧
      ¬HalfPureSingletonFanFin10Atom0394 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0394 HalfPureSingletonFanFin10Atom0898 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301, halfPureSingletonFanFin10_capSet_iff_mask0301] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06950 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0898 χ ∧
      ¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0017
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0898 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0301, halfPureSingletonFanFin10_capSet_iff_mask0301] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06961 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0395 χ ∧
      ¬HalfPureSingletonFanFin10Atom0150 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0395 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06962 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0395 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0395 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06963 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0395 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0395 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06964 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0395 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0178 HalfPureSingletonFanFin10Atom0395 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06965 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0395 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0395 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06967 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0647 χ ∧
      ¬HalfPureSingletonFanFin10Atom0395 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0395 HalfPureSingletonFanFin10Atom0647 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557, halfPureSingletonFanFin10_cupSet_iff_mask0557] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06968 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0647 χ ∧
      HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0017
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0647 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557, halfPureSingletonFanFin10_cupSet_iff_mask0557] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06978 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0395 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0647 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0395
    HalfPureSingletonFanFin10Atom0647 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557, halfPureSingletonFanFin10_cupSet_iff_mask0557] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06979 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0899 χ ∧
      ¬HalfPureSingletonFanFin10Atom0395 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0395 HalfPureSingletonFanFin10Atom0899 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557, halfPureSingletonFanFin10_capSet_iff_mask0557] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06980 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0899 χ ∧
      ¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0011
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0017
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0030
    HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0899 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0557, halfPureSingletonFanFin10_capSet_iff_mask0557] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause06991 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0396 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0396 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06992 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0396 χ ∧
      ¬HalfPureSingletonFanFin10Atom0152 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0152 HalfPureSingletonFanFin10Atom0396 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06993 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0396 χ ∧
      ¬HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0164 HalfPureSingletonFanFin10Atom0396 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06994 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0396 χ ∧
      ¬HalfPureSingletonFanFin10Atom0179 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0396 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06995 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0396 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0396 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause06997 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0648 χ ∧
      ¬HalfPureSingletonFanFin10Atom0396 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0396 HalfPureSingletonFanFin10Atom0648 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205, halfPureSingletonFanFin10_cupSet_iff_mask0205] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07009 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0900 χ ∧
      ¬HalfPureSingletonFanFin10Atom0396 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0396 HalfPureSingletonFanFin10Atom0900 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0205, halfPureSingletonFanFin10_capSet_iff_mask0205] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07021 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0397 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0397 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07022 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0397 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0397 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07023 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0397 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0165 HalfPureSingletonFanFin10Atom0397 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07024 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0397 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0397 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07025 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0397 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0397 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07027 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0649 χ ∧
      ¬HalfPureSingletonFanFin10Atom0397 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0397 HalfPureSingletonFanFin10Atom0649 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333, halfPureSingletonFanFin10_cupSet_iff_mask0333] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07028 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0649 χ ∧
      HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0649 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333, halfPureSingletonFanFin10_cupSet_iff_mask0333] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07039 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0901 χ ∧
      ¬HalfPureSingletonFanFin10Atom0397 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0397 HalfPureSingletonFanFin10Atom0901 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333, halfPureSingletonFanFin10_capSet_iff_mask0333] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07040 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0901 χ ∧
      ¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0901 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0333, halfPureSingletonFanFin10_capSet_iff_mask0333] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07051 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0398 χ ∧
      ¬HalfPureSingletonFanFin10Atom0151 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0398 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07052 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0398 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0398 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589] at hbad
  tauto

end ErdosSzekeres

end
