module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 58. -/

theorem halfPureSingletonFanFin10_clause12007 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0815 χ ∧
      ¬HalfPureSingletonFanFin10Atom0563 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0563 HalfPureSingletonFanFin10Atom0815 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376, halfPureSingletonFanFin10_cupSet_iff_mask0376] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12008 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0815 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0087 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0087
    HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0091
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0096
    HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0815 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376, halfPureSingletonFanFin10_cupSet_iff_mask0376] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12019 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0563 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0563 HalfPureSingletonFanFin10Atom1067 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376, halfPureSingletonFanFin10_capSet_iff_mask0376] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12032 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0564 χ ∧
      ¬HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0299 HalfPureSingletonFanFin10Atom0564 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0632] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12034 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0564 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0308 HalfPureSingletonFanFin10Atom0564 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0632] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12037 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0816 χ ∧
      ¬HalfPureSingletonFanFin10Atom0564 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0564 HalfPureSingletonFanFin10Atom0816 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0632, halfPureSingletonFanFin10_cupSet_iff_mask0632] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12049 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0564 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0564 HalfPureSingletonFanFin10Atom1068 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0632, halfPureSingletonFanFin10_capSet_iff_mask0632] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12061 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0565 χ ∧
      ¬HalfPureSingletonFanFin10Atom0297 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0297 HalfPureSingletonFanFin10Atom0565 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12062 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0565 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0298 HalfPureSingletonFanFin10Atom0565 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12063 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0565 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0565 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12064 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0565 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0565 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12065 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0565 χ ∧
      ¬HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0319 HalfPureSingletonFanFin10Atom0565 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12066 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0565 χ ∧
      HalfPureSingletonFanFin10Atom0297 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0297 HalfPureSingletonFanFin10Atom0298
    HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0309
    HalfPureSingletonFanFin10Atom0319 HalfPureSingletonFanFin10Atom0565 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12067 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0817 χ ∧
      ¬HalfPureSingletonFanFin10Atom0565 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0565 HalfPureSingletonFanFin10Atom0817 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440, halfPureSingletonFanFin10_cupSet_iff_mask0440] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12079 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0565 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0565 HalfPureSingletonFanFin10Atom1069 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0440, halfPureSingletonFanFin10_capSet_iff_mask0440] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12092 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0566 χ ∧
      ¬HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0299 HalfPureSingletonFanFin10Atom0566 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12093 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0566 χ ∧
      ¬HalfPureSingletonFanFin10Atom0304 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0304 HalfPureSingletonFanFin10Atom0566 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12094 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0566 χ ∧
      ¬HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0566 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12095 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0566 χ ∧
      ¬HalfPureSingletonFanFin10Atom0320 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0320 HalfPureSingletonFanFin10Atom0566 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12097 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0818 χ ∧
      ¬HalfPureSingletonFanFin10Atom0566 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0566 HalfPureSingletonFanFin10Atom0818 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696, halfPureSingletonFanFin10_cupSet_iff_mask0696] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12098 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0818 χ ∧
      HalfPureSingletonFanFin10Atom0086 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0115 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0088
    HalfPureSingletonFanFin10Atom0090 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0099
    HalfPureSingletonFanFin10Atom0102 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0109 HalfPureSingletonFanFin10Atom0115
    HalfPureSingletonFanFin10Atom0818 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696, halfPureSingletonFanFin10_cupSet_iff_mask0696] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12109 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0566 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0566 HalfPureSingletonFanFin10Atom1070 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0696, halfPureSingletonFanFin10_capSet_iff_mask0696] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12121 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0567 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0298 HalfPureSingletonFanFin10Atom0567 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12122 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0567 χ ∧
      ¬HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0299 HalfPureSingletonFanFin10Atom0567 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12123 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0567 χ ∧
      ¬HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0567 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12124 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0567 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0567 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12125 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0567 χ ∧
      ¬HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0321 HalfPureSingletonFanFin10Atom0567 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12127 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0819 χ ∧
      ¬HalfPureSingletonFanFin10Atom0567 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0567 HalfPureSingletonFanFin10Atom0819 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824, halfPureSingletonFanFin10_cupSet_iff_mask0824] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12140 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0086 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0090 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0094 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom1071 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0824, halfPureSingletonFanFin10_capSet_iff_mask0824] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12151 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0568 χ ∧
      ¬HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0300 HalfPureSingletonFanFin10Atom0568 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12152 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0568 χ ∧
      ¬HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0301 HalfPureSingletonFanFin10Atom0568 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12153 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0568 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0568 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472] at hbad
  tauto

end ErdosSzekeres

end
