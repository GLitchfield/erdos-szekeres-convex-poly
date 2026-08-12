module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 61. -/

theorem halfPureSingletonFanFin10_clause12427 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0829 χ ∧
      ¬HalfPureSingletonFanFin10Atom0577 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0577 HalfPureSingletonFanFin10Atom0829 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0496, halfPureSingletonFanFin10_cupSet_iff_mask0496] at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12439 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0577 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0577 HalfPureSingletonFanFin10Atom1081 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0496, halfPureSingletonFanFin10_capSet_iff_mask0496] at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12452 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0578 χ ∧
      ¬HalfPureSingletonFanFin10Atom0318 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0318 HalfPureSingletonFanFin10Atom0578 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0752] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12454 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0578 χ ∧
      ¬HalfPureSingletonFanFin10Atom0323 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0323 HalfPureSingletonFanFin10Atom0578 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0752] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12457 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0830 χ ∧
      ¬HalfPureSingletonFanFin10Atom0578 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0578 HalfPureSingletonFanFin10Atom0830 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0752, halfPureSingletonFanFin10_cupSet_iff_mask0752] at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12483 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0579 χ ∧
      ¬HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0321 HalfPureSingletonFanFin10Atom0579 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0880] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12484 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0579 χ ∧
      ¬HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0324 HalfPureSingletonFanFin10Atom0579 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0880] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12485 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0579 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0328 HalfPureSingletonFanFin10Atom0579 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0880] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12487 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0831 χ ∧
      ¬HalfPureSingletonFanFin10Atom0579 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0579 HalfPureSingletonFanFin10Atom0831 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0880, halfPureSingletonFanFin10_cupSet_iff_mask0880] at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12500 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1083 χ ∧
      ¬HalfPureSingletonFanFin10Atom0101 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ ∧
      ¬HalfPureSingletonFanFin10Atom0107 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0101 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0104 HalfPureSingletonFanFin10Atom0106
    HalfPureSingletonFanFin10Atom0107 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom1083 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0880, halfPureSingletonFanFin10_capSet_iff_mask0880] at hbad
  cases hcolor0 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12512 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0580 χ ∧
      ¬HalfPureSingletonFanFin10Atom0320 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0320 HalfPureSingletonFanFin10Atom0580 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0944] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12513 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0580 χ ∧
      ¬HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0321 HalfPureSingletonFanFin10Atom0580 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0944] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12514 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0580 χ ∧
      ¬HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0325 HalfPureSingletonFanFin10Atom0580 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0944] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12515 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0580 χ ∧
      ¬HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0329 HalfPureSingletonFanFin10Atom0580 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0944] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12517 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0832 χ ∧
      ¬HalfPureSingletonFanFin10Atom0580 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0580 HalfPureSingletonFanFin10Atom0832 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0944, halfPureSingletonFanFin10_cupSet_iff_mask0944] at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12529 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0580 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0580 HalfPureSingletonFanFin10Atom1084 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0944, halfPureSingletonFanFin10_capSet_iff_mask0944] at hbad
  cases hcolor0 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12541 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0581 χ ∧
      ¬HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0322 HalfPureSingletonFanFin10Atom0581 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12542 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0581 χ ∧
      ¬HalfPureSingletonFanFin10Atom0323 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0323 HalfPureSingletonFanFin10Atom0581 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12543 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0581 χ ∧
      ¬HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0324 HalfPureSingletonFanFin10Atom0581 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12544 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0581 χ ∧
      ¬HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0325 HalfPureSingletonFanFin10Atom0581 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12545 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0581 χ ∧
      ¬HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0330 HalfPureSingletonFanFin10Atom0581 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12547 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0833 χ ∧
      ¬HalfPureSingletonFanFin10Atom0581 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0581 HalfPureSingletonFanFin10Atom0833 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976, halfPureSingletonFanFin10_cupSet_iff_mask0976] at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12559 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0581 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0581 HalfPureSingletonFanFin10Atom1085 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0976, halfPureSingletonFanFin10_capSet_iff_mask0976] at hbad
  cases hcolor0 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12571 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0582 χ ∧
      ¬HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0326 HalfPureSingletonFanFin10Atom0582 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12572 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0582 χ ∧
      ¬HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0327 HalfPureSingletonFanFin10Atom0582 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12573 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0582 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0328 HalfPureSingletonFanFin10Atom0582 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12574 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0582 χ ∧
      ¬HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0329 HalfPureSingletonFanFin10Atom0582 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12575 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0582 χ ∧
      ¬HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0330 HalfPureSingletonFanFin10Atom0582 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12589 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0582 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0582 HalfPureSingletonFanFin10Atom1086 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992, halfPureSingletonFanFin10_capSet_iff_mask0992] at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12590 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1086 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0114 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0117 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ ∧
      ¬HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0113 HalfPureSingletonFanFin10Atom0114
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0116
    HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom1086 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0992, halfPureSingletonFanFin10_capSet_iff_mask0992] at hbad
  cases hcolor0 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12681 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0150 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ ∧
      HalfPureSingletonFanFin10Atom0152 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ ∧
      HalfPureSingletonFanFin10Atom0161 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ ∧
      HalfPureSingletonFanFin10Atom0179 χ ∧
      HalfPureSingletonFanFin10Atom0195 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 7}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0151
    HalfPureSingletonFanFin10Atom0152 HalfPureSingletonFanFin10Atom0160
    HalfPureSingletonFanFin10Atom0161 HalfPureSingletonFanFin10Atom0164
    HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0176
    HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0195
    HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0267
    HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0286
    HalfPureSingletonFanFin10Atom0306 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12682 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0150 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 5, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0151
    HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0160
    HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0165
    HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0177
    HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0196
    HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0268
    HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0287
    HalfPureSingletonFanFin10Atom0307 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
