module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 45. -/

theorem halfPureSingletonFanFin10_clause07473 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0412 χ ∧
      ¬HalfPureSingletonFanFin10Atom0164 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0164 HalfPureSingletonFanFin10Atom0412 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07474 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0412 χ ∧
      ¬HalfPureSingletonFanFin10Atom0195 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0412 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07475 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0412 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0412 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07477 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0664 χ ∧
      ¬HalfPureSingletonFanFin10Atom0412 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0412 HalfPureSingletonFanFin10Atom0664 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229, halfPureSingletonFanFin10_cupSet_iff_mask0229] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07489 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0916 χ ∧
      ¬HalfPureSingletonFanFin10Atom0412 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0412 HalfPureSingletonFanFin10Atom0916 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229, halfPureSingletonFanFin10_capSet_iff_mask0229] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07490 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0916 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0013 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0028 χ ∧
      ¬HalfPureSingletonFanFin10Atom0031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0013 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0031
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0916 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0229, halfPureSingletonFanFin10_capSet_iff_mask0229] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07501 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0413 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0413 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07502 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0413 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0413 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07503 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0413 χ ∧
      ¬HalfPureSingletonFanFin10Atom0165 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0165 HalfPureSingletonFanFin10Atom0413 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07504 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0413 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0196 HalfPureSingletonFanFin10Atom0413 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07505 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0413 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0413 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07507 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0665 χ ∧
      ¬HalfPureSingletonFanFin10Atom0413 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0413 HalfPureSingletonFanFin10Atom0665 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357, halfPureSingletonFanFin10_cupSet_iff_mask0357] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07508 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0665 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0665 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357, halfPureSingletonFanFin10_cupSet_iff_mask0357] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07519 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0917 χ ∧
      ¬HalfPureSingletonFanFin10Atom0413 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0413 HalfPureSingletonFanFin10Atom0917 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357, halfPureSingletonFanFin10_capSet_iff_mask0357] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07520 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0917 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0014 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0917 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0357, halfPureSingletonFanFin10_capSet_iff_mask0357] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07531 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0414 χ ∧
      ¬HalfPureSingletonFanFin10Atom0160 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0414 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07532 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0414 χ ∧
      ¬HalfPureSingletonFanFin10Atom0163 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0414 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07533 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0414 χ ∧
      ¬HalfPureSingletonFanFin10Atom0166 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0414 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07534 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0414 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0197 HalfPureSingletonFanFin10Atom0414 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07535 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0414 χ ∧
      ¬HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0288 HalfPureSingletonFanFin10Atom0414 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07537 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0666 χ ∧
      ¬HalfPureSingletonFanFin10Atom0414 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0414 HalfPureSingletonFanFin10Atom0666 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613, halfPureSingletonFanFin10_cupSet_iff_mask0613] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07538 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0666 χ ∧
      HalfPureSingletonFanFin10Atom0011 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0030 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0666 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613, halfPureSingletonFanFin10_cupSet_iff_mask0613] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07549 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0918 χ ∧
      ¬HalfPureSingletonFanFin10Atom0414 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0414 HalfPureSingletonFanFin10Atom0918 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613, halfPureSingletonFanFin10_capSet_iff_mask0613] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07550 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0918 χ ∧
      ¬HalfPureSingletonFanFin10Atom0011 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0011 HalfPureSingletonFanFin10Atom0012
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0033
    HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0079
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0918 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0613, halfPureSingletonFanFin10_capSet_iff_mask0613] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07561 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0415 χ ∧
      ¬HalfPureSingletonFanFin10Atom0161 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0161 HalfPureSingletonFanFin10Atom0415 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07562 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0415 χ ∧
      ¬HalfPureSingletonFanFin10Atom0162 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0415 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07563 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0415 χ ∧
      ¬HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0167 HalfPureSingletonFanFin10Atom0415 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07564 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0415 χ ∧
      ¬HalfPureSingletonFanFin10Atom0198 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0198 HalfPureSingletonFanFin10Atom0415 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07565 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0415 χ ∧
      ¬HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0415 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07567 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0667 χ ∧
      ¬HalfPureSingletonFanFin10Atom0415 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0415 HalfPureSingletonFanFin10Atom0667 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421, halfPureSingletonFanFin10_cupSet_iff_mask0421] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07579 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0919 χ ∧
      ¬HalfPureSingletonFanFin10Atom0415 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0415 HalfPureSingletonFanFin10Atom0919 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0421, halfPureSingletonFanFin10_capSet_iff_mask0421] at hbad
  cases hcolor0 : χ ⟨0, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07591 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0416 χ ∧
      ¬HalfPureSingletonFanFin10Atom0161 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0161 HalfPureSingletonFanFin10Atom0416 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0677] at hbad
  tauto

end ErdosSzekeres

end
