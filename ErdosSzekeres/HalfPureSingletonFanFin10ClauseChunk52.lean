module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 52. -/

theorem halfPureSingletonFanFin10_clause11167 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0787 χ ∧
      ¬HalfPureSingletonFanFin10Atom0535 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0535 HalfPureSingletonFanFin10Atom0787 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0668, halfPureSingletonFanFin10_cupSet_iff_mask0668] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11180 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1039 χ ∧
      ¬HalfPureSingletonFanFin10Atom0065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0068 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0088 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0099 χ ∧
      ¬HalfPureSingletonFanFin10Atom0109 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0065 HalfPureSingletonFanFin10Atom0068
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0075 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0088 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0099 HalfPureSingletonFanFin10Atom0109
    HalfPureSingletonFanFin10Atom1039 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0668, halfPureSingletonFanFin10_capSet_iff_mask0668] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11191 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0536 χ ∧
      ¬HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0536 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0796] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11194 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0536 χ ∧
      ¬HalfPureSingletonFanFin10Atom0285 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0285 HalfPureSingletonFanFin10Atom0536 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0796] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11195 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0536 χ ∧
      ¬HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0536 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0796] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11197 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0788 χ ∧
      ¬HalfPureSingletonFanFin10Atom0536 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0536 HalfPureSingletonFanFin10Atom0788 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0796, halfPureSingletonFanFin10_cupSet_iff_mask0796] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11221 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0537 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0537 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11222 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0537 χ ∧
      ¬HalfPureSingletonFanFin10Atom0267 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0537 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11223 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0537 χ ∧
      ¬HalfPureSingletonFanFin10Atom0270 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0537 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11224 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0537 χ ∧
      ¬HalfPureSingletonFanFin10Atom0286 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0537 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11225 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0537 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0537 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11227 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0789 χ ∧
      ¬HalfPureSingletonFanFin10Atom0537 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0537 HalfPureSingletonFanFin10Atom0789 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236, halfPureSingletonFanFin10_cupSet_iff_mask0236] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11228 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0789 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0068 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0077 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0068 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0077 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0789 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236, halfPureSingletonFanFin10_cupSet_iff_mask0236] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11239 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1041 χ ∧
      ¬HalfPureSingletonFanFin10Atom0537 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0537 HalfPureSingletonFanFin10Atom1041 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0236, halfPureSingletonFanFin10_capSet_iff_mask0236] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11251 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0538 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0538 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11252 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0538 χ ∧
      ¬HalfPureSingletonFanFin10Atom0268 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0538 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11253 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0538 χ ∧
      ¬HalfPureSingletonFanFin10Atom0271 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0538 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11254 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0538 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0538 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11255 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0538 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0538 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11257 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0790 χ ∧
      ¬HalfPureSingletonFanFin10Atom0538 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0538 HalfPureSingletonFanFin10Atom0790 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364, halfPureSingletonFanFin10_cupSet_iff_mask0364] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11258 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0790 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0069 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0790 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364, halfPureSingletonFanFin10_cupSet_iff_mask0364] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11269 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1042 χ ∧
      ¬HalfPureSingletonFanFin10Atom0538 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0538 HalfPureSingletonFanFin10Atom1042 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364, halfPureSingletonFanFin10_capSet_iff_mask0364] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11270 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1042 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0069 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0069 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom1042 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0364, halfPureSingletonFanFin10_capSet_iff_mask0364] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11281 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0539 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0539 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11282 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0539 χ ∧
      ¬HalfPureSingletonFanFin10Atom0269 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0539 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11283 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0539 χ ∧
      ¬HalfPureSingletonFanFin10Atom0272 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0539 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11284 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0539 χ ∧
      ¬HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0288 HalfPureSingletonFanFin10Atom0539 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11285 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0539 χ ∧
      ¬HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0308 HalfPureSingletonFanFin10Atom0539 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11287 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0791 χ ∧
      ¬HalfPureSingletonFanFin10Atom0539 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0539 HalfPureSingletonFanFin10Atom0791 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620, halfPureSingletonFanFin10_cupSet_iff_mask0620] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11288 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0791 χ ∧
      HalfPureSingletonFanFin10Atom0066 χ ∧
      HalfPureSingletonFanFin10Atom0067 χ ∧
      HalfPureSingletonFanFin10Atom0070 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0094 χ ∧
      HalfPureSingletonFanFin10Atom0097 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0791 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620, halfPureSingletonFanFin10_cupSet_iff_mask0620] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11299 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1043 χ ∧
      ¬HalfPureSingletonFanFin10Atom0539 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0539 HalfPureSingletonFanFin10Atom1043 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620, halfPureSingletonFanFin10_capSet_iff_mask0620] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11300 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1043 χ ∧
      ¬HalfPureSingletonFanFin10Atom0066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0067 χ ∧
      ¬HalfPureSingletonFanFin10Atom0070 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0094 χ ∧
      ¬HalfPureSingletonFanFin10Atom0097 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0066 HalfPureSingletonFanFin10Atom0067
    HalfPureSingletonFanFin10Atom0070 HalfPureSingletonFanFin10Atom0076
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0094
    HalfPureSingletonFanFin10Atom0097 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom1043 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0620, halfPureSingletonFanFin10_capSet_iff_mask0620] at hbad
  cases hcolor0 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
