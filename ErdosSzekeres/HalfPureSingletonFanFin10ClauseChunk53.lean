module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 53. -/

theorem halfPureSingletonFanFin10_clause11311 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0540 χ ∧
      ¬HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0540 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11312 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0540 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0540 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11313 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0540 χ ∧
      ¬HalfPureSingletonFanFin10Atom0273 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0540 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11314 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0540 χ ∧
      ¬HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0540 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11315 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0540 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0540 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11316 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0540 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0268
    HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0289
    HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0540 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11317 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0792 χ ∧
      ¬HalfPureSingletonFanFin10Atom0540 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0540 HalfPureSingletonFanFin10Atom0792 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428, halfPureSingletonFanFin10_cupSet_iff_mask0428] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11318 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0792 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0792 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428, halfPureSingletonFanFin10_cupSet_iff_mask0428] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11329 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1044 χ ∧
      ¬HalfPureSingletonFanFin10Atom0540 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0540 HalfPureSingletonFanFin10Atom1044 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428, halfPureSingletonFanFin10_capSet_iff_mask0428] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11330 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1044 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom1044 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0428, halfPureSingletonFanFin10_capSet_iff_mask0428] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11341 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0541 χ ∧
      ¬HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0541 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11342 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0541 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0541 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11343 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0541 χ ∧
      ¬HalfPureSingletonFanFin10Atom0274 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0541 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11344 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0541 χ ∧
      ¬HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0290 HalfPureSingletonFanFin10Atom0541 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11345 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0541 χ ∧
      ¬HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0541 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11347 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0793 χ ∧
      ¬HalfPureSingletonFanFin10Atom0541 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0541 HalfPureSingletonFanFin10Atom0793 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684, halfPureSingletonFanFin10_cupSet_iff_mask0684] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11359 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1045 χ ∧
      ¬HalfPureSingletonFanFin10Atom0541 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0541 HalfPureSingletonFanFin10Atom1045 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0684, halfPureSingletonFanFin10_capSet_iff_mask0684] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11371 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0542 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0542 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11372 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0542 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0542 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11373 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0542 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0542 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11374 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0542 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0542 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11375 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0542 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0542 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11377 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0794 χ ∧
      ¬HalfPureSingletonFanFin10Atom0542 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0542 HalfPureSingletonFanFin10Atom0794 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812, halfPureSingletonFanFin10_cupSet_iff_mask0812] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11378 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0794 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0794 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812, halfPureSingletonFanFin10_cupSet_iff_mask0812] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11389 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1046 χ ∧
      ¬HalfPureSingletonFanFin10Atom0542 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0542 HalfPureSingletonFanFin10Atom1046 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812, halfPureSingletonFanFin10_capSet_iff_mask0812] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11390 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1046 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom1046 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0812, halfPureSingletonFanFin10_capSet_iff_mask0812] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11401 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0543 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0543 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11402 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0543 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0543 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11403 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0543 χ ∧
      ¬HalfPureSingletonFanFin10Atom0273 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0543 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11404 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0543 χ ∧
      ¬HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0543 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11405 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0543 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0543 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11407 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0795 χ ∧
      ¬HalfPureSingletonFanFin10Atom0543 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0543 HalfPureSingletonFanFin10Atom0795 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460, halfPureSingletonFanFin10_cupSet_iff_mask0460] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
