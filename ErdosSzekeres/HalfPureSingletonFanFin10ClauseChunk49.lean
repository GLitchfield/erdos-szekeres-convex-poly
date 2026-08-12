module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 49. -/

theorem halfPureSingletonFanFin10_clause08255 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0438 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0438 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08257 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0690 χ ∧
      ¬HalfPureSingletonFanFin10Atom0438 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0438 HalfPureSingletonFanFin10Atom0690 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457, halfPureSingletonFanFin10_cupSet_iff_mask0457] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08269 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0942 χ ∧
      ¬HalfPureSingletonFanFin10Atom0438 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0438 HalfPureSingletonFanFin10Atom0942 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457, halfPureSingletonFanFin10_capSet_iff_mask0457] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08281 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0439 χ ∧
      ¬HalfPureSingletonFanFin10Atom0179 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0439 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08282 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0439 χ ∧
      ¬HalfPureSingletonFanFin10Atom0181 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0439 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08283 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0439 χ ∧
      ¬HalfPureSingletonFanFin10Atom0183 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0183 HalfPureSingletonFanFin10Atom0439 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08284 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0439 χ ∧
      ¬HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0202 HalfPureSingletonFanFin10Atom0439 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08285 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0439 χ ∧
      ¬HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0313 HalfPureSingletonFanFin10Atom0439 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08287 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0691 χ ∧
      ¬HalfPureSingletonFanFin10Atom0439 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0439 HalfPureSingletonFanFin10Atom0691 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713, halfPureSingletonFanFin10_cupSet_iff_mask0713] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08299 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0943 χ ∧
      ¬HalfPureSingletonFanFin10Atom0439 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0439 HalfPureSingletonFanFin10Atom0943 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0713, halfPureSingletonFanFin10_capSet_iff_mask0713] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08311 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0440 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0440 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08312 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0440 χ ∧
      ¬HalfPureSingletonFanFin10Atom0181 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0440 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08313 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0440 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0440 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08314 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0440 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0203 HalfPureSingletonFanFin10Atom0440 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08315 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0440 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0440 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08317 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0692 χ ∧
      ¬HalfPureSingletonFanFin10Atom0440 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0440 HalfPureSingletonFanFin10Atom0692 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841, halfPureSingletonFanFin10_cupSet_iff_mask0841] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08318 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0692 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0692 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841, halfPureSingletonFanFin10_cupSet_iff_mask0841] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08329 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0944 χ ∧
      ¬HalfPureSingletonFanFin10Atom0440 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0440 HalfPureSingletonFanFin10Atom0944 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841, halfPureSingletonFanFin10_capSet_iff_mask0841] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08330 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0944 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0018 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0944 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0841, halfPureSingletonFanFin10_capSet_iff_mask0841] at hbad
  cases hcolor0 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08343 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0441 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0441 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0905] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08344 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0441 χ ∧
      ¬HalfPureSingletonFanFin10Atom0204 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0204 HalfPureSingletonFanFin10Atom0441 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0905] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08345 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0441 χ ∧
      ¬HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0315 HalfPureSingletonFanFin10Atom0441 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0905] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08347 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0693 χ ∧
      ¬HalfPureSingletonFanFin10Atom0441 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0441 HalfPureSingletonFanFin10Atom0693 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0905, halfPureSingletonFanFin10_cupSet_iff_mask0905] at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08359 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0945 χ ∧
      ¬HalfPureSingletonFanFin10Atom0441 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0441 HalfPureSingletonFanFin10Atom0945 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0905, halfPureSingletonFanFin10_capSet_iff_mask0905] at hbad
  cases hcolor0 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08671 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0452 χ ∧
      ¬HalfPureSingletonFanFin10Atom0195 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0452 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0481] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08672 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0452 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0196 HalfPureSingletonFanFin10Atom0452 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0481] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08674 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0452 χ ∧
      ¬HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0201 HalfPureSingletonFanFin10Atom0452 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0481] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08675 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0452 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0326 HalfPureSingletonFanFin10Atom0452 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0481] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08677 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0704 χ ∧
      ¬HalfPureSingletonFanFin10Atom0452 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0452 HalfPureSingletonFanFin10Atom0704 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0481, halfPureSingletonFanFin10_cupSet_iff_mask0481] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08689 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0956 χ ∧
      ¬HalfPureSingletonFanFin10Atom0452 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0452 HalfPureSingletonFanFin10Atom0956 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0481, halfPureSingletonFanFin10_capSet_iff_mask0481] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08701 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0453 χ ∧
      ¬HalfPureSingletonFanFin10Atom0195 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0453 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08702 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0453 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0197 HalfPureSingletonFanFin10Atom0453 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737] at hbad
  tauto

end ErdosSzekeres

end
