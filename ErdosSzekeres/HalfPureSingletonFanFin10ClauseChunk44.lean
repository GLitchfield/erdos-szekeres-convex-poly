module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 44. -/

theorem halfPureSingletonFanFin10_clause07053 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0398 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0398 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07054 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0398 χ ∧
      ¬HalfPureSingletonFanFin10Atom0181 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0398 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07055 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0398 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0398 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07057 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0650 χ ∧
      ¬HalfPureSingletonFanFin10Atom0398 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0398 HalfPureSingletonFanFin10Atom0650 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589, halfPureSingletonFanFin10_cupSet_iff_mask0589] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07058 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0650 χ ∧
      HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0650 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589, halfPureSingletonFanFin10_cupSet_iff_mask0589] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07069 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0902 χ ∧
      ¬HalfPureSingletonFanFin10Atom0398 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0398 HalfPureSingletonFanFin10Atom0902 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589, halfPureSingletonFanFin10_capSet_iff_mask0589] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07070 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0902 χ ∧
      ¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0902 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0589, halfPureSingletonFanFin10_capSet_iff_mask0589] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07081 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0399 χ ∧
      ¬HalfPureSingletonFanFin10Atom0152 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0152 HalfPureSingletonFanFin10Atom0399 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07082 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0399 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0399 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07083 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0399 χ ∧
      ¬HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0167 HalfPureSingletonFanFin10Atom0399 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07084 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0399 χ ∧
      ¬HalfPureSingletonFanFin10Atom0182 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0182 HalfPureSingletonFanFin10Atom0399 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07085 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0399 χ ∧
      ¬HalfPureSingletonFanFin10Atom0273 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0399 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07087 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0651 χ ∧
      ¬HalfPureSingletonFanFin10Atom0399 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0399 HalfPureSingletonFanFin10Atom0651 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397, halfPureSingletonFanFin10_cupSet_iff_mask0397] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07099 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0903 χ ∧
      ¬HalfPureSingletonFanFin10Atom0399 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0399 HalfPureSingletonFanFin10Atom0903 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0397, halfPureSingletonFanFin10_capSet_iff_mask0397] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07111 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0400 χ ∧
      ¬HalfPureSingletonFanFin10Atom0152 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0152 HalfPureSingletonFanFin10Atom0400 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07112 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0400 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0400 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07113 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0400 χ ∧
      ¬HalfPureSingletonFanFin10Atom0168 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0168 HalfPureSingletonFanFin10Atom0400 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07114 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0400 χ ∧
      ¬HalfPureSingletonFanFin10Atom0183 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0183 HalfPureSingletonFanFin10Atom0400 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07115 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0400 χ ∧
      ¬HalfPureSingletonFanFin10Atom0274 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0400 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07117 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0652 χ ∧
      ¬HalfPureSingletonFanFin10Atom0400 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0400 HalfPureSingletonFanFin10Atom0652 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653, halfPureSingletonFanFin10_cupSet_iff_mask0653] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07129 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0904 χ ∧
      ¬HalfPureSingletonFanFin10Atom0400 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0400 HalfPureSingletonFanFin10Atom0904 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0653, halfPureSingletonFanFin10_capSet_iff_mask0653] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07141 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0401 χ ∧
      ¬HalfPureSingletonFanFin10Atom0153 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0401 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07142 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0401 χ ∧
      ¬HalfPureSingletonFanFin10Atom0154 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0401 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07143 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0401 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0169 HalfPureSingletonFanFin10Atom0401 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07144 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0401 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0401 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07145 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0401 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0401 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07147 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0653 χ ∧
      ¬HalfPureSingletonFanFin10Atom0401 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0401 HalfPureSingletonFanFin10Atom0653 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781, halfPureSingletonFanFin10_cupSet_iff_mask0781] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07148 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0653 χ ∧
      HalfPureSingletonFanFin10Atom0009 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0653 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781, halfPureSingletonFanFin10_cupSet_iff_mask0781] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07159 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0905 χ ∧
      ¬HalfPureSingletonFanFin10Atom0401 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0401 HalfPureSingletonFanFin10Atom0905 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781, halfPureSingletonFanFin10_capSet_iff_mask0781] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07160 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0905 χ ∧
      ¬HalfPureSingletonFanFin10Atom0009 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0009 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0070
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0905 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0781, halfPureSingletonFanFin10_capSet_iff_mask0781] at hbad
  cases hcolor0 : χ ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07471 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0412 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0412 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07472 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0412 χ ∧
      ¬HalfPureSingletonFanFin10Atom0161 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0161 HalfPureSingletonFanFin10Atom0412 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229] at hbad
  tauto

end ErdosSzekeres

end
