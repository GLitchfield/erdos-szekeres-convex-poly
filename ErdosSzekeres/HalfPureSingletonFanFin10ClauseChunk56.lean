module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 56. -/

theorem halfPureSingletonFanFin10_clause11707 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0805 χ ∧
      ¬HalfPureSingletonFanFin10Atom0553 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0553 HalfPureSingletonFanFin10Atom0805 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468, halfPureSingletonFanFin10_cupSet_iff_mask0468] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11719 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1057 χ ∧
      ¬HalfPureSingletonFanFin10Atom0553 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0553 HalfPureSingletonFanFin10Atom1057 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0468, halfPureSingletonFanFin10_capSet_iff_mask0468] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11734 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0554 χ ∧
      ¬HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0293 HalfPureSingletonFanFin10Atom0554 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0724] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11737 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0806 χ ∧
      ¬HalfPureSingletonFanFin10Atom0554 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0554 HalfPureSingletonFanFin10Atom0806 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0724, halfPureSingletonFanFin10_cupSet_iff_mask0724] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11749 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1058 χ ∧
      ¬HalfPureSingletonFanFin10Atom0554 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0554 HalfPureSingletonFanFin10Atom1058 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0724, halfPureSingletonFanFin10_capSet_iff_mask0724] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11761 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0555 χ ∧
      ¬HalfPureSingletonFanFin10Atom0281 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0555 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0852] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11762 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0555 χ ∧
      ¬HalfPureSingletonFanFin10Atom0282 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0282 HalfPureSingletonFanFin10Atom0555 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0852] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11764 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0555 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0555 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0852] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11767 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0807 χ ∧
      ¬HalfPureSingletonFanFin10Atom0555 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0555 HalfPureSingletonFanFin10Atom0807 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0852, halfPureSingletonFanFin10_cupSet_iff_mask0852] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11779 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1059 χ ∧
      ¬HalfPureSingletonFanFin10Atom0555 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0555 HalfPureSingletonFanFin10Atom1059 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0852, halfPureSingletonFanFin10_capSet_iff_mask0852] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11780 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1059 χ ∧
      ¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0106 HalfPureSingletonFanFin10Atom0107
    HalfPureSingletonFanFin10Atom0110 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom1059 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0852, halfPureSingletonFanFin10_capSet_iff_mask0852] at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11791 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0556 χ ∧
      ¬HalfPureSingletonFanFin10Atom0283 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0283 HalfPureSingletonFanFin10Atom0556 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11792 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0556 χ ∧
      ¬HalfPureSingletonFanFin10Atom0284 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0284 HalfPureSingletonFanFin10Atom0556 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11793 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0556 χ ∧
      ¬HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0285 HalfPureSingletonFanFin10Atom0556 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11794 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0556 χ ∧
      ¬HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0295 HalfPureSingletonFanFin10Atom0556 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11795 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0556 χ ∧
      ¬HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0325 HalfPureSingletonFanFin10Atom0556 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11797 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0808 χ ∧
      ¬HalfPureSingletonFanFin10Atom0556 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0556 HalfPureSingletonFanFin10Atom0808 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916, halfPureSingletonFanFin10_cupSet_iff_mask0916] at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11809 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1060 χ ∧
      ¬HalfPureSingletonFanFin10Atom0556 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0556 HalfPureSingletonFanFin10Atom1060 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0916, halfPureSingletonFanFin10_capSet_iff_mask0916] at hbad
  cases hcolor0 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11821 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0557 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0557 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11822 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0557 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0557 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11823 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0557 χ ∧
      ¬HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0557 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11824 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0557 χ ∧
      ¬HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0557 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11825 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0557 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0326 HalfPureSingletonFanFin10Atom0557 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11827 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0809 χ ∧
      ¬HalfPureSingletonFanFin10Atom0557 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0557 HalfPureSingletonFanFin10Atom0809 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484, halfPureSingletonFanFin10_cupSet_iff_mask0484] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11839 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1061 χ ∧
      ¬HalfPureSingletonFanFin10Atom0557 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0557 HalfPureSingletonFanFin10Atom1061 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484, halfPureSingletonFanFin10_capSet_iff_mask0484] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11840 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1061 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0083
    HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0114 HalfPureSingletonFanFin10Atom0117
    HalfPureSingletonFanFin10Atom1061 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0484, halfPureSingletonFanFin10_capSet_iff_mask0484] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11851 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0558 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0558 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11852 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0558 χ ∧
      ¬HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0288 HalfPureSingletonFanFin10Atom0558 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11853 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0558 χ ∧
      ¬HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0290 HalfPureSingletonFanFin10Atom0558 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11854 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0558 χ ∧
      ¬HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0293 HalfPureSingletonFanFin10Atom0558 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11855 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0558 χ ∧
      ¬HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0327 HalfPureSingletonFanFin10Atom0558 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11857 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0810 χ ∧
      ¬HalfPureSingletonFanFin10Atom0558 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0558 HalfPureSingletonFanFin10Atom0810 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740, halfPureSingletonFanFin10_cupSet_iff_mask0740] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
