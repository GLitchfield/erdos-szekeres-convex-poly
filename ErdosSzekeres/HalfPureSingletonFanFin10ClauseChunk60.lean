module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 60. -/

theorem halfPureSingletonFanFin10_clause12306 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0573 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0308
    HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0313
    HalfPureSingletonFanFin10Atom0327 HalfPureSingletonFanFin10Atom0573 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12307 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0825 χ ∧
      ¬HalfPureSingletonFanFin10Atom0573 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0573 HalfPureSingletonFanFin10Atom0825 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744, halfPureSingletonFanFin10_cupSet_iff_mask0744] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12319 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0573 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0573 HalfPureSingletonFanFin10Atom1077 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744, halfPureSingletonFanFin10_capSet_iff_mask0744] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12331 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0574 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0574 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12332 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0574 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0308 HalfPureSingletonFanFin10Atom0574 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12333 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0574 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0574 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12334 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0574 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0574 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12335 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0574 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0328 HalfPureSingletonFanFin10Atom0574 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12337 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0826 χ ∧
      ¬HalfPureSingletonFanFin10Atom0574 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0574 HalfPureSingletonFanFin10Atom0826 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872, halfPureSingletonFanFin10_cupSet_iff_mask0872] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12338 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0826 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0826 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872, halfPureSingletonFanFin10_cupSet_iff_mask0872] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12349 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0574 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0574 HalfPureSingletonFanFin10Atom1078 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872, halfPureSingletonFanFin10_capSet_iff_mask0872] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12350 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom1078 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0872, halfPureSingletonFanFin10_capSet_iff_mask0872] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12361 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0575 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0575 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12362 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0575 χ ∧
      ¬HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0575 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12363 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0575 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0575 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12364 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0575 χ ∧
      ¬HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0315 HalfPureSingletonFanFin10Atom0575 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12365 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0575 χ ∧
      ¬HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0329 HalfPureSingletonFanFin10Atom0575 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12367 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0827 χ ∧
      ¬HalfPureSingletonFanFin10Atom0575 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0575 HalfPureSingletonFanFin10Atom0827 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936, halfPureSingletonFanFin10_cupSet_iff_mask0936] at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12379 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0575 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0575 HalfPureSingletonFanFin10Atom1079 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936, halfPureSingletonFanFin10_capSet_iff_mask0936] at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12380 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0092 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom1079 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0936, halfPureSingletonFanFin10_capSet_iff_mask0936] at hbad
  cases hcolor0 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12391 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0576 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0576 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12392 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0576 χ ∧
      ¬HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0313 HalfPureSingletonFanFin10Atom0576 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12393 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0576 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0576 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12394 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0576 χ ∧
      ¬HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0315 HalfPureSingletonFanFin10Atom0576 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12395 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0576 χ ∧
      ¬HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0330 HalfPureSingletonFanFin10Atom0576 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12396 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0576 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0313
    HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0315
    HalfPureSingletonFanFin10Atom0330 HalfPureSingletonFanFin10Atom0576 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12397 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0828 χ ∧
      ¬HalfPureSingletonFanFin10Atom0576 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0576 HalfPureSingletonFanFin10Atom0828 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968, halfPureSingletonFanFin10_cupSet_iff_mask0968] at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12409 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0576 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0576 HalfPureSingletonFanFin10Atom1080 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0968, halfPureSingletonFanFin10_capSet_iff_mask0968] at hbad
  cases hcolor0 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12421 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0577 χ ∧
      ¬HalfPureSingletonFanFin10Atom0316 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0316 HalfPureSingletonFanFin10Atom0577 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0496] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12422 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0577 χ ∧
      ¬HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0317 HalfPureSingletonFanFin10Atom0577 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0496] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12424 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0577 χ ∧
      ¬HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0322 HalfPureSingletonFanFin10Atom0577 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0496] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12425 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0577 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0326 HalfPureSingletonFanFin10Atom0577 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0496] at hbad
  tauto

end ErdosSzekeres

end
