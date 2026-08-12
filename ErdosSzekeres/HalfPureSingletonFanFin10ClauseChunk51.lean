module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 51. -/

theorem halfPureSingletonFanFin10_clause10983 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0529 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0529 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10984 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0529 χ ∧
      ¬HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0278 HalfPureSingletonFanFin10Atom0529 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10985 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0529 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0298 HalfPureSingletonFanFin10Atom0529 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10987 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0781 χ ∧
      ¬HalfPureSingletonFanFin10Atom0529 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0529 HalfPureSingletonFanFin10Atom0781 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316, halfPureSingletonFanFin10_cupSet_iff_mask0316] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause10999 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0529 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0529 HalfPureSingletonFanFin10Atom1033 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316, halfPureSingletonFanFin10_capSet_iff_mask0316] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11011 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0530 χ ∧
      ¬HalfPureSingletonFanFin10Atom0261 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0261 HalfPureSingletonFanFin10Atom0530 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0572] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11012 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0530 χ ∧
      ¬HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0265 HalfPureSingletonFanFin10Atom0530 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0572] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11014 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0530 χ ∧
      ¬HalfPureSingletonFanFin10Atom0279 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0279 HalfPureSingletonFanFin10Atom0530 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0572] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11015 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0530 χ ∧
      ¬HalfPureSingletonFanFin10Atom0299 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0299 HalfPureSingletonFanFin10Atom0530 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0572] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11017 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0782 χ ∧
      ¬HalfPureSingletonFanFin10Atom0530 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0530 HalfPureSingletonFanFin10Atom0782 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0572, halfPureSingletonFanFin10_cupSet_iff_mask0572] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11041 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0531 χ ∧
      ¬HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0262 HalfPureSingletonFanFin10Atom0531 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0220] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11042 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0531 χ ∧
      ¬HalfPureSingletonFanFin10Atom0263 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0263 HalfPureSingletonFanFin10Atom0531 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0220] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11059 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1035 χ ∧
      ¬HalfPureSingletonFanFin10Atom0531 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0531 HalfPureSingletonFanFin10Atom1035 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0220, halfPureSingletonFanFin10_capSet_iff_mask0220] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11071 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0532 χ ∧
      ¬HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0262 HalfPureSingletonFanFin10Atom0532 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0348] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11072 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0532 χ ∧
      ¬HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0532 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0348] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11074 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0532 χ ∧
      ¬HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0532 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0348] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11075 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0532 χ ∧
      ¬HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0301 HalfPureSingletonFanFin10Atom0532 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0348] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11077 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0784 χ ∧
      ¬HalfPureSingletonFanFin10Atom0532 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0532 HalfPureSingletonFanFin10Atom0784 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0348, halfPureSingletonFanFin10_cupSet_iff_mask0348] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11089 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0532 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0532 HalfPureSingletonFanFin10Atom1036 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0348, halfPureSingletonFanFin10_capSet_iff_mask0348] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11102 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0533 χ ∧
      ¬HalfPureSingletonFanFin10Atom0265 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0265 HalfPureSingletonFanFin10Atom0533 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0604] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11103 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0533 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0533 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0604] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11105 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0533 χ ∧
      ¬HalfPureSingletonFanFin10Atom0302 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0302 HalfPureSingletonFanFin10Atom0533 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0604] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11107 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0785 χ ∧
      ¬HalfPureSingletonFanFin10Atom0533 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0533 HalfPureSingletonFanFin10Atom0785 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0604, halfPureSingletonFanFin10_cupSet_iff_mask0604] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11131 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0534 χ ∧
      ¬HalfPureSingletonFanFin10Atom0263 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0263 HalfPureSingletonFanFin10Atom0534 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11132 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0534 χ ∧
      ¬HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0534 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11133 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0534 χ ∧
      ¬HalfPureSingletonFanFin10Atom0273 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0534 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11134 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0534 χ ∧
      ¬HalfPureSingletonFanFin10Atom0283 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0283 HalfPureSingletonFanFin10Atom0534 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11137 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0786 χ ∧
      ¬HalfPureSingletonFanFin10Atom0534 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0534 HalfPureSingletonFanFin10Atom0786 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412, halfPureSingletonFanFin10_cupSet_iff_mask0412] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11149 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1038 χ ∧
      ¬HalfPureSingletonFanFin10Atom0534 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0534 HalfPureSingletonFanFin10Atom1038 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412, halfPureSingletonFanFin10_capSet_iff_mask0412] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11150 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1038 χ ∧
      ¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0098 χ ∧
      ¬HalfPureSingletonFanFin10Atom0108 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0074 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0089
    HalfPureSingletonFanFin10Atom0098 HalfPureSingletonFanFin10Atom0108
    HalfPureSingletonFanFin10Atom1038 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0412, halfPureSingletonFanFin10_capSet_iff_mask0412] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11161 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0535 χ ∧
      ¬HalfPureSingletonFanFin10Atom0263 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0263 HalfPureSingletonFanFin10Atom0535 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0668] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11163 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0535 χ ∧
      ¬HalfPureSingletonFanFin10Atom0274 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0535 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0668] at hbad
  tauto

end ErdosSzekeres

end
