module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 54. -/

theorem halfPureSingletonFanFin10_clause11408 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0795 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0795 at hbad
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

theorem halfPureSingletonFanFin10_clause11419 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1047 χ ∧
      ¬HalfPureSingletonFanFin10Atom0543 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0543 HalfPureSingletonFanFin10Atom1047 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460, halfPureSingletonFanFin10_capSet_iff_mask0460] at hbad
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

theorem halfPureSingletonFanFin10_clause11420 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1047 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom1047 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0460, halfPureSingletonFanFin10_capSet_iff_mask0460] at hbad
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

theorem halfPureSingletonFanFin10_clause11431 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0544 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0544 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11432 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0544 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0544 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11433 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0544 χ ∧
      ¬HalfPureSingletonFanFin10Atom0274 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0544 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11434 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0544 χ ∧
      ¬HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0293 HalfPureSingletonFanFin10Atom0544 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11435 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0544 χ ∧
      ¬HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0313 HalfPureSingletonFanFin10Atom0544 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11437 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0796 χ ∧
      ¬HalfPureSingletonFanFin10Atom0544 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0544 HalfPureSingletonFanFin10Atom0796 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716, halfPureSingletonFanFin10_cupSet_iff_mask0716] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11449 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1048 χ ∧
      ¬HalfPureSingletonFanFin10Atom0544 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0544 HalfPureSingletonFanFin10Atom1048 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0716, halfPureSingletonFanFin10_capSet_iff_mask0716] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11461 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0545 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0545 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11462 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0545 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0545 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11463 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0545 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0545 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11464 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0545 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0545 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11465 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0545 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0545 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11467 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0797 χ ∧
      ¬HalfPureSingletonFanFin10Atom0545 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0545 HalfPureSingletonFanFin10Atom0797 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844, halfPureSingletonFanFin10_cupSet_iff_mask0844] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11468 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0797 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0797 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844, halfPureSingletonFanFin10_cupSet_iff_mask0844] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11479 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1049 χ ∧
      ¬HalfPureSingletonFanFin10Atom0545 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0545 HalfPureSingletonFanFin10Atom1049 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844, halfPureSingletonFanFin10_capSet_iff_mask0844] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11480 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1049 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0067 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0097
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom1049 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0844, halfPureSingletonFanFin10_capSet_iff_mask0844] at hbad
  cases hcolor0 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11491 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0546 χ ∧
      ¬HalfPureSingletonFanFin10Atom0273 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0546 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11492 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0546 χ ∧
      ¬HalfPureSingletonFanFin10Atom0274 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0546 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11493 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0546 χ ∧
      ¬HalfPureSingletonFanFin10Atom0275 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0546 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11494 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0546 χ ∧
      ¬HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0295 HalfPureSingletonFanFin10Atom0546 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11495 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0546 χ ∧
      ¬HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0315 HalfPureSingletonFanFin10Atom0546 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11497 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0798 χ ∧
      ¬HalfPureSingletonFanFin10Atom0546 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0546 HalfPureSingletonFanFin10Atom0798 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908, halfPureSingletonFanFin10_cupSet_iff_mask0908] at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11498 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0798 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0083 χ ∧
      HalfPureSingletonFanFin10Atom0084 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0068 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0798 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908, halfPureSingletonFanFin10_cupSet_iff_mask0908] at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11509 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1050 χ ∧
      ¬HalfPureSingletonFanFin10Atom0546 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0546 HalfPureSingletonFanFin10Atom1050 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908, halfPureSingletonFanFin10_capSet_iff_mask0908] at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11510 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1050 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0068 HalfPureSingletonFanFin10Atom0069
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0084 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom1050 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0908, halfPureSingletonFanFin10_capSet_iff_mask0908] at hbad
  cases hcolor0 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11521 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0547 χ ∧
      ¬HalfPureSingletonFanFin10Atom0276 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0276 HalfPureSingletonFanFin10Atom0547 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11522 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0547 χ ∧
      ¬HalfPureSingletonFanFin10Atom0277 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0277 HalfPureSingletonFanFin10Atom0547 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11523 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0547 χ ∧
      ¬HalfPureSingletonFanFin10Atom0280 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0280 HalfPureSingletonFanFin10Atom0547 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11524 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0547 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0547 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244] at hbad
  tauto

end ErdosSzekeres

end
