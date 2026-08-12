module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 57. -/

theorem halfPureSingletonFanFin10_clause11869 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1062 χ ∧
      ¬HalfPureSingletonFanFin10Atom0558 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0558 HalfPureSingletonFanFin10Atom1062 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740, halfPureSingletonFanFin10_capSet_iff_mask0740] at hbad
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

theorem halfPureSingletonFanFin10_clause11870 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1062 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0077 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0084 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0115 χ ∧
      ¬HalfPureSingletonFanFin10Atom0118 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0077
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0080
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0084
    HalfPureSingletonFanFin10Atom0111 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0115 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom1062 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0740, halfPureSingletonFanFin10_capSet_iff_mask0740] at hbad
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

theorem halfPureSingletonFanFin10_clause11881 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0559 χ ∧
      ¬HalfPureSingletonFanFin10Atom0287 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0559 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11882 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0559 χ ∧
      ¬HalfPureSingletonFanFin10Atom0288 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0288 HalfPureSingletonFanFin10Atom0559 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11883 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0559 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0559 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11884 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0559 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0559 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11885 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0559 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0328 HalfPureSingletonFanFin10Atom0559 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11887 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0811 χ ∧
      ¬HalfPureSingletonFanFin10Atom0559 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0559 HalfPureSingletonFanFin10Atom0811 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868, halfPureSingletonFanFin10_cupSet_iff_mask0868] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11888 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0811 χ ∧
      HalfPureSingletonFanFin10Atom0076 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0113 χ ∧
      HalfPureSingletonFanFin10Atom0116 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0811 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868, halfPureSingletonFanFin10_cupSet_iff_mask0868] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11899 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1063 χ ∧
      ¬HalfPureSingletonFanFin10Atom0559 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0559 HalfPureSingletonFanFin10Atom1063 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868, halfPureSingletonFanFin10_capSet_iff_mask0868] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11900 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1063 χ ∧
      ¬HalfPureSingletonFanFin10Atom0076 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0076 HalfPureSingletonFanFin10Atom0078
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0081
    HalfPureSingletonFanFin10Atom0082 HalfPureSingletonFanFin10Atom0085
    HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom1063 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0868, halfPureSingletonFanFin10_capSet_iff_mask0868] at hbad
  cases hcolor0 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11911 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0560 χ ∧
      ¬HalfPureSingletonFanFin10Atom0289 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0560 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11912 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0560 χ ∧
      ¬HalfPureSingletonFanFin10Atom0290 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0290 HalfPureSingletonFanFin10Atom0560 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11913 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0560 χ ∧
      ¬HalfPureSingletonFanFin10Atom0291 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0560 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11914 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0560 χ ∧
      ¬HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0295 HalfPureSingletonFanFin10Atom0560 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11915 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0560 χ ∧
      ¬HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0329 HalfPureSingletonFanFin10Atom0560 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11917 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0812 χ ∧
      ¬HalfPureSingletonFanFin10Atom0560 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0560 HalfPureSingletonFanFin10Atom0812 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932, halfPureSingletonFanFin10_cupSet_iff_mask0932] at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11929 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1064 χ ∧
      ¬HalfPureSingletonFanFin10Atom0560 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0560 HalfPureSingletonFanFin10Atom1064 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0932, halfPureSingletonFanFin10_capSet_iff_mask0932] at hbad
  cases hcolor0 : χ ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11941 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0561 χ ∧
      ¬HalfPureSingletonFanFin10Atom0292 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0561 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11942 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0561 χ ∧
      ¬HalfPureSingletonFanFin10Atom0293 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0293 HalfPureSingletonFanFin10Atom0561 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11943 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0561 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0561 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11944 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0561 χ ∧
      ¬HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0295 HalfPureSingletonFanFin10Atom0561 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11945 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0561 χ ∧
      ¬HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0330 HalfPureSingletonFanFin10Atom0561 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11947 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0813 χ ∧
      ¬HalfPureSingletonFanFin10Atom0561 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0561 HalfPureSingletonFanFin10Atom0813 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964, halfPureSingletonFanFin10_cupSet_iff_mask0964] at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11959 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1065 χ ∧
      ¬HalfPureSingletonFanFin10Atom0561 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0561 HalfPureSingletonFanFin10Atom1065 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0964, halfPureSingletonFanFin10_capSet_iff_mask0964] at hbad
  cases hcolor0 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause11973 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0562 χ ∧
      ¬HalfPureSingletonFanFin10Atom0300 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0300 HalfPureSingletonFanFin10Atom0562 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0248] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause11989 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1066 χ ∧
      ¬HalfPureSingletonFanFin10Atom0562 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0562 HalfPureSingletonFanFin10Atom1066 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0248, halfPureSingletonFanFin10_capSet_iff_mask0248] at hbad
  cases hcolor0 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨4, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12001 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0563 χ ∧
      ¬HalfPureSingletonFanFin10Atom0296 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0296 HalfPureSingletonFanFin10Atom0563 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12002 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0563 χ ∧
      ¬HalfPureSingletonFanFin10Atom0298 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0298 HalfPureSingletonFanFin10Atom0563 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12003 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0563 χ ∧
      ¬HalfPureSingletonFanFin10Atom0301 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0301 HalfPureSingletonFanFin10Atom0563 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12004 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0563 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0563 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause12005 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0563 χ ∧
      ¬HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0317 HalfPureSingletonFanFin10Atom0563 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0376] at hbad
  tauto

end ErdosSzekeres

end
