module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 48. -/

theorem halfPureSingletonFanFin10_clause08135 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0434 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0308 HalfPureSingletonFanFin10Atom0434 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08137 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0686 χ ∧
      ¬HalfPureSingletonFanFin10Atom0434 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0434 HalfPureSingletonFanFin10Atom0686 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617, halfPureSingletonFanFin10_cupSet_iff_mask0617] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08138 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0686 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0686 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617, halfPureSingletonFanFin10_cupSet_iff_mask0617] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08148 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0434 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0686 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0113 HalfPureSingletonFanFin10Atom0434
    HalfPureSingletonFanFin10Atom0686 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617, halfPureSingletonFanFin10_cupSet_iff_mask0617] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08149 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0938 χ ∧
      ¬HalfPureSingletonFanFin10Atom0434 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0434 HalfPureSingletonFanFin10Atom0938 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617, halfPureSingletonFanFin10_capSet_iff_mask0617] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08150 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0938 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0938 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617, halfPureSingletonFanFin10_capSet_iff_mask0617] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08161 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0435 χ ∧
      ¬HalfPureSingletonFanFin10Atom0176 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0176 HalfPureSingletonFanFin10Atom0435 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0425] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08162 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0435 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0435 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0425] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08164 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0435 χ ∧
      ¬HalfPureSingletonFanFin10Atom0198 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0198 HalfPureSingletonFanFin10Atom0435 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0425] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08165 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0435 χ ∧
      ¬HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0435 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0425] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08167 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0687 χ ∧
      ¬HalfPureSingletonFanFin10Atom0435 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0435 HalfPureSingletonFanFin10Atom0687 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0425, halfPureSingletonFanFin10_cupSet_iff_mask0425] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08179 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0939 χ ∧
      ¬HalfPureSingletonFanFin10Atom0435 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0435 HalfPureSingletonFanFin10Atom0939 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0425, halfPureSingletonFanFin10_capSet_iff_mask0425] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08191 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0436 χ ∧
      ¬HalfPureSingletonFanFin10Atom0176 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0176 HalfPureSingletonFanFin10Atom0436 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0681] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08192 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0436 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0178 HalfPureSingletonFanFin10Atom0436 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0681] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08194 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0436 χ ∧
      ¬HalfPureSingletonFanFin10Atom0199 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0199 HalfPureSingletonFanFin10Atom0436 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0681] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08195 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0436 χ ∧
      ¬HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0436 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0681] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08197 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0688 χ ∧
      ¬HalfPureSingletonFanFin10Atom0436 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0436 HalfPureSingletonFanFin10Atom0688 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0681, halfPureSingletonFanFin10_cupSet_iff_mask0681] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08209 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0940 χ ∧
      ¬HalfPureSingletonFanFin10Atom0436 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0436 HalfPureSingletonFanFin10Atom0940 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0681, halfPureSingletonFanFin10_capSet_iff_mask0681] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08221 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0437 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0437 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08222 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0437 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0178 HalfPureSingletonFanFin10Atom0437 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08223 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0437 χ ∧
      ¬HalfPureSingletonFanFin10Atom0184 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0437 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08224 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0437 χ ∧
      ¬HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0437 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08225 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0437 χ ∧
      ¬HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0437 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08226 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0437 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0178
    HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0200
    HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0437 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08227 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0689 χ ∧
      ¬HalfPureSingletonFanFin10Atom0437 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0437 HalfPureSingletonFanFin10Atom0689 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809, halfPureSingletonFanFin10_cupSet_iff_mask0809] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08228 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0689 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0021 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0689 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809, halfPureSingletonFanFin10_cupSet_iff_mask0809] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08239 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0941 χ ∧
      ¬HalfPureSingletonFanFin10Atom0437 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0437 HalfPureSingletonFanFin10Atom0941 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809, halfPureSingletonFanFin10_capSet_iff_mask0809] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08240 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0941 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0021 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0020
    HalfPureSingletonFanFin10Atom0021 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0093 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0941 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0809, halfPureSingletonFanFin10_capSet_iff_mask0809] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08251 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0438 χ ∧
      ¬HalfPureSingletonFanFin10Atom0179 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0438 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08252 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0438 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0438 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08253 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0438 χ ∧
      ¬HalfPureSingletonFanFin10Atom0182 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0182 HalfPureSingletonFanFin10Atom0438 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08254 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0438 χ ∧
      ¬HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0201 HalfPureSingletonFanFin10Atom0438 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0457] at hbad
  tauto

end ErdosSzekeres

end
