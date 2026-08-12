module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 59. -/

theorem halfPureSingletonFanFin10_clause12154 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0568 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0568 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12155 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0568 χ ∧
      ¬HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0322 HalfPureSingletonFanFin10Atom0568 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12157 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0820 χ ∧
      ¬HalfPureSingletonFanFin10Atom0568 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0568 HalfPureSingletonFanFin10Atom0820 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472, halfPureSingletonFanFin10_cupSet_iff_mask0472] at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12169 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0568 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0568 HalfPureSingletonFanFin10Atom1072 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0472, halfPureSingletonFanFin10_capSet_iff_mask0472] at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12212 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0570 χ ∧
      ¬HalfPureSingletonFanFin10Atom0302 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0302 HalfPureSingletonFanFin10Atom0570 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0856] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12213 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0570 χ ∧
      ¬HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0570 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0856] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12214 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0570 χ ∧
      ¬HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0570 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0856] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12215 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0570 χ ∧
      ¬HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0324 HalfPureSingletonFanFin10Atom0570 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0856] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12217 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0822 χ ∧
      ¬HalfPureSingletonFanFin10Atom0570 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0570 HalfPureSingletonFanFin10Atom0822 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0856, halfPureSingletonFanFin10_cupSet_iff_mask0856] at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12229 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0570 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0570 HalfPureSingletonFanFin10Atom1074 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0856, halfPureSingletonFanFin10_capSet_iff_mask0856] at hbad
  cases hcolor0 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12241 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0571 χ ∧
      ¬HalfPureSingletonFanFin10Atom0303 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0571 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12242 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0571 χ ∧
      ¬HalfPureSingletonFanFin10Atom0304 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0304 HalfPureSingletonFanFin10Atom0571 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12243 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0571 χ ∧
      ¬HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0571 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12244 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0571 χ ∧
      ¬HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0315 HalfPureSingletonFanFin10Atom0571 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12245 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0571 χ ∧
      ¬HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0325 HalfPureSingletonFanFin10Atom0571 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12247 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0823 χ ∧
      ¬HalfPureSingletonFanFin10Atom0571 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0571 HalfPureSingletonFanFin10Atom0823 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920, halfPureSingletonFanFin10_cupSet_iff_mask0920] at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12248 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0823 χ ∧
      HalfPureSingletonFanFin10Atom0088 χ ∧
      HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0099 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0108 χ ∧
      HalfPureSingletonFanFin10Atom0109 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0090 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0823 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920, halfPureSingletonFanFin10_cupSet_iff_mask0920] at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12259 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0571 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0571 HalfPureSingletonFanFin10Atom1075 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920, halfPureSingletonFanFin10_capSet_iff_mask0920] at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12260 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0090 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0100
    HalfPureSingletonFanFin10Atom0108 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom1075 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0920, halfPureSingletonFanFin10_capSet_iff_mask0920] at hbad
  cases hcolor0 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12271 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0572 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0572 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12272 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0572 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0572 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12273 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0572 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0572 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12274 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0572 χ ∧
      ¬HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0572 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12275 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0572 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0326 HalfPureSingletonFanFin10Atom0572 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12277 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0824 χ ∧
      ¬HalfPureSingletonFanFin10Atom0572 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0572 HalfPureSingletonFanFin10Atom0824 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488, halfPureSingletonFanFin10_cupSet_iff_mask0488] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12278 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0824 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0098 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0114 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0095
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0098
    HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom0824 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488, halfPureSingletonFanFin10_cupSet_iff_mask0488] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12289 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0572 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0572 HalfPureSingletonFanFin10Atom1076 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0488, halfPureSingletonFanFin10_capSet_iff_mask0488] at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12301 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0573 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0573 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12302 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0573 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0308 HalfPureSingletonFanFin10Atom0573 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12303 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0573 χ ∧
      ¬HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0573 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12304 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0573 χ ∧
      ¬HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0313 HalfPureSingletonFanFin10Atom0573 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12305 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0573 χ ∧
      ¬HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0327 HalfPureSingletonFanFin10Atom0573 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0744] at hbad
  tauto

end ErdosSzekeres

end
