module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 55. -/

theorem halfPureSingletonFanFin10_clause11525 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0547 χ ∧
      ¬HalfPureSingletonFanFin10Atom0316 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0316 HalfPureSingletonFanFin10Atom0547 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11527 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0799 χ ∧
      ¬HalfPureSingletonFanFin10Atom0547 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0547 HalfPureSingletonFanFin10Atom0799 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244, halfPureSingletonFanFin10_cupSet_iff_mask0244] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11528 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0799 χ ∧
      HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0101 χ ∧
      HalfPureSingletonFanFin10Atom0102 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0072
    HalfPureSingletonFanFin10Atom0073 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0102
    HalfPureSingletonFanFin10Atom0105 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0799 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244, halfPureSingletonFanFin10_cupSet_iff_mask0244] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11539 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1051 χ ∧
      ¬HalfPureSingletonFanFin10Atom0547 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0547 HalfPureSingletonFanFin10Atom1051 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0244, halfPureSingletonFanFin10_capSet_iff_mask0244] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11551 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0548 χ ∧
      ¬HalfPureSingletonFanFin10Atom0276 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0276 HalfPureSingletonFanFin10Atom0548 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0372] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11552 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0548 χ ∧
      ¬HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0278 HalfPureSingletonFanFin10Atom0548 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0372] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11553 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0548 χ ∧
      ¬HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0548 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0372] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11554 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0548 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0548 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0372] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11555 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0548 χ ∧
      ¬HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0317 HalfPureSingletonFanFin10Atom0548 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0372] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11557 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0800 χ ∧
      ¬HalfPureSingletonFanFin10Atom0548 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0548 HalfPureSingletonFanFin10Atom0800 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0372, halfPureSingletonFanFin10_cupSet_iff_mask0372] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11583 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0549 χ ∧
      ¬HalfPureSingletonFanFin10Atom0282 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0282 HalfPureSingletonFanFin10Atom0549 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0628] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11585 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0549 χ ∧
      ¬HalfPureSingletonFanFin10Atom0318 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0318 HalfPureSingletonFanFin10Atom0549 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0628] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11587 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0801 χ ∧
      ¬HalfPureSingletonFanFin10Atom0549 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0549 HalfPureSingletonFanFin10Atom0801 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0628, halfPureSingletonFanFin10_cupSet_iff_mask0628] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11611 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0550 χ ∧
      ¬HalfPureSingletonFanFin10Atom0277 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0277 HalfPureSingletonFanFin10Atom0550 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0436] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11612 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0550 χ ∧
      ¬HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0278 HalfPureSingletonFanFin10Atom0550 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0436] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11615 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0550 χ ∧
      ¬HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0319 HalfPureSingletonFanFin10Atom0550 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0436] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11617 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0802 χ ∧
      ¬HalfPureSingletonFanFin10Atom0550 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0550 HalfPureSingletonFanFin10Atom0802 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0436, halfPureSingletonFanFin10_cupSet_iff_mask0436] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11629 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1054 χ ∧
      ¬HalfPureSingletonFanFin10Atom0550 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0550 HalfPureSingletonFanFin10Atom1054 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0436, halfPureSingletonFanFin10_capSet_iff_mask0436] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11641 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0551 χ ∧
      ¬HalfPureSingletonFanFin10Atom0277 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0277 HalfPureSingletonFanFin10Atom0551 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0692] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11659 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1055 χ ∧
      ¬HalfPureSingletonFanFin10Atom0551 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0551 HalfPureSingletonFanFin10Atom1055 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0692, halfPureSingletonFanFin10_capSet_iff_mask0692] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11671 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0552 χ ∧
      ¬HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0278 HalfPureSingletonFanFin10Atom0552 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11672 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0552 χ ∧
      ¬HalfPureSingletonFanFin10Atom0279 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0279 HalfPureSingletonFanFin10Atom0552 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11673 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0552 χ ∧
      ¬HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0285 HalfPureSingletonFanFin10Atom0552 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11674 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0552 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0552 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11675 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0552 χ ∧
      ¬HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0321 HalfPureSingletonFanFin10Atom0552 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11689 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1056 χ ∧
      ¬HalfPureSingletonFanFin10Atom0552 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0552 HalfPureSingletonFanFin10Atom1056 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820, halfPureSingletonFanFin10_capSet_iff_mask0820] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11690 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1056 χ ∧
      ¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0103 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom1056 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0820, halfPureSingletonFanFin10_capSet_iff_mask0820] at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11701 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0553 χ ∧
      ¬HalfPureSingletonFanFin10Atom0280 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0280 HalfPureSingletonFanFin10Atom0553 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11702 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0553 χ ∧
      ¬HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0553 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11703 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0553 χ ∧
      ¬HalfPureSingletonFanFin10Atom0283 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0283 HalfPureSingletonFanFin10Atom0553 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11704 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0553 χ ∧
      ¬HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0553 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11705 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0553 χ ∧
      ¬HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0322 HalfPureSingletonFanFin10Atom0553 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468] at hbad
  tauto

end ErdosSzekeres

end
