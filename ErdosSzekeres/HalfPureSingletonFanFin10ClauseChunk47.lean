module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 47. -/

theorem halfPureSingletonFanFin10_clause07715 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0420 χ ∧
      ¬HalfPureSingletonFanFin10Atom0294 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0420 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07717 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0672 χ ∧
      ¬HalfPureSingletonFanFin10Atom0420 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0420 HalfPureSingletonFanFin10Atom0672 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837, halfPureSingletonFanFin10_cupSet_iff_mask0837] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07718 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0672 χ ∧
      HalfPureSingletonFanFin10Atom0012 χ ∧
      HalfPureSingletonFanFin10Atom0014 χ ∧
      HalfPureSingletonFanFin10Atom0015 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0082 χ ∧
      HalfPureSingletonFanFin10Atom0085 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0672 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837, halfPureSingletonFanFin10_cupSet_iff_mask0837] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07729 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0924 χ ∧
      ¬HalfPureSingletonFanFin10Atom0420 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0420 HalfPureSingletonFanFin10Atom0924 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837, halfPureSingletonFanFin10_capSet_iff_mask0837] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07730 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0924 χ ∧
      ¬HalfPureSingletonFanFin10Atom0012 χ ∧
      ¬HalfPureSingletonFanFin10Atom0014 χ ∧
      ¬HalfPureSingletonFanFin10Atom0015 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0082 χ ∧
      ¬HalfPureSingletonFanFin10Atom0085 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0012 HalfPureSingletonFanFin10Atom0014
    HalfPureSingletonFanFin10Atom0015 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0082
    HalfPureSingletonFanFin10Atom0085 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0924 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0837, halfPureSingletonFanFin10_capSet_iff_mask0837] at hbad
  cases hcolor0 : χ ⟨0, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07741 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0421 χ ∧
      ¬HalfPureSingletonFanFin10Atom0167 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0167 HalfPureSingletonFanFin10Atom0421 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0901] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07743 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0421 χ ∧
      ¬HalfPureSingletonFanFin10Atom0169 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0169 HalfPureSingletonFanFin10Atom0421 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0901] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07744 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0421 χ ∧
      ¬HalfPureSingletonFanFin10Atom0204 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0204 HalfPureSingletonFanFin10Atom0421 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0901] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07745 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0421 χ ∧
      ¬HalfPureSingletonFanFin10Atom0295 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0295 HalfPureSingletonFanFin10Atom0421 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0901] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause07747 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0673 χ ∧
      ¬HalfPureSingletonFanFin10Atom0421 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0421 HalfPureSingletonFanFin10Atom0673 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0901, halfPureSingletonFanFin10_cupSet_iff_mask0901] at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause07759 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0925 χ ∧
      ¬HalfPureSingletonFanFin10Atom0421 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0421 HalfPureSingletonFanFin10Atom0925 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0901, halfPureSingletonFanFin10_capSet_iff_mask0901] at hbad
  cases hcolor0 : χ ⟨0, 2, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨2, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨2, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨2, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08071 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0432 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0432 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08072 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0432 χ ∧
      ¬HalfPureSingletonFanFin10Atom0176 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0176 HalfPureSingletonFanFin10Atom0432 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08073 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0432 χ ∧
      ¬HalfPureSingletonFanFin10Atom0179 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0432 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08074 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0432 χ ∧
      ¬HalfPureSingletonFanFin10Atom0195 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0432 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08075 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0432 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0432 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08077 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0684 χ ∧
      ¬HalfPureSingletonFanFin10Atom0432 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0432 HalfPureSingletonFanFin10Atom0684 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233, halfPureSingletonFanFin10_cupSet_iff_mask0233] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08078 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0684 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0019 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0028 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0019 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0028 HalfPureSingletonFanFin10Atom0031
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0684 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233, halfPureSingletonFanFin10_cupSet_iff_mask0233] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08089 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0936 χ ∧
      ¬HalfPureSingletonFanFin10Atom0432 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0432 HalfPureSingletonFanFin10Atom0936 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0233, halfPureSingletonFanFin10_capSet_iff_mask0233] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08101 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0433 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0433 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08102 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0433 χ ∧
      ¬HalfPureSingletonFanFin10Atom0177 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0433 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08103 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0433 χ ∧
      ¬HalfPureSingletonFanFin10Atom0180 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0433 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08104 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0433 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0196 HalfPureSingletonFanFin10Atom0433 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08105 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0433 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0433 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08107 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0685 χ ∧
      ¬HalfPureSingletonFanFin10Atom0433 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0433 HalfPureSingletonFanFin10Atom0685 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361, halfPureSingletonFanFin10_cupSet_iff_mask0361] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08108 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0685 χ ∧
      HalfPureSingletonFanFin10Atom0017 χ ∧
      HalfPureSingletonFanFin10Atom0018 χ ∧
      HalfPureSingletonFanFin10Atom0020 χ ∧
      HalfPureSingletonFanFin10Atom0027 χ ∧
      HalfPureSingletonFanFin10Atom0029 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0685 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361, halfPureSingletonFanFin10_cupSet_iff_mask0361] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08119 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0937 χ ∧
      ¬HalfPureSingletonFanFin10Atom0433 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0433 HalfPureSingletonFanFin10Atom0937 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361, halfPureSingletonFanFin10_capSet_iff_mask0361] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08120 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0937 χ ∧
      ¬HalfPureSingletonFanFin10Atom0017 χ ∧
      ¬HalfPureSingletonFanFin10Atom0018 χ ∧
      ¬HalfPureSingletonFanFin10Atom0020 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0017 HalfPureSingletonFanFin10Atom0018
    HalfPureSingletonFanFin10Atom0020 HalfPureSingletonFanFin10Atom0027
    HalfPureSingletonFanFin10Atom0029 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0937 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0361, halfPureSingletonFanFin10_capSet_iff_mask0361] at hbad
  cases hcolor0 : χ ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08131 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0434 χ ∧
      ¬HalfPureSingletonFanFin10Atom0175 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0434 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08132 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0434 χ ∧
      ¬HalfPureSingletonFanFin10Atom0178 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0178 HalfPureSingletonFanFin10Atom0434 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08133 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0434 χ ∧
      ¬HalfPureSingletonFanFin10Atom0181 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0434 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08134 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0434 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0197 HalfPureSingletonFanFin10Atom0434 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0617] at hbad
  tauto

end ErdosSzekeres

end
