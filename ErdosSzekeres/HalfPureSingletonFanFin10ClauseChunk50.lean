module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 50. -/

theorem halfPureSingletonFanFin10_clause08703 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0453 χ ∧
      ¬HalfPureSingletonFanFin10Atom0199 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0199 HalfPureSingletonFanFin10Atom0453 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08704 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0453 χ ∧
      ¬HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0202 HalfPureSingletonFanFin10Atom0453 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08705 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0453 χ ∧
      ¬HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0327 HalfPureSingletonFanFin10Atom0453 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08707 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0705 χ ∧
      ¬HalfPureSingletonFanFin10Atom0453 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0453 HalfPureSingletonFanFin10Atom0705 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737, halfPureSingletonFanFin10_cupSet_iff_mask0737] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08719 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0957 χ ∧
      ¬HalfPureSingletonFanFin10Atom0453 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0453 HalfPureSingletonFanFin10Atom0957 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0737, halfPureSingletonFanFin10_capSet_iff_mask0737] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08731 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0454 χ ∧
      ¬HalfPureSingletonFanFin10Atom0196 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0196 HalfPureSingletonFanFin10Atom0454 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08732 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0454 χ ∧
      ¬HalfPureSingletonFanFin10Atom0197 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0197 HalfPureSingletonFanFin10Atom0454 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08733 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0454 χ ∧
      ¬HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0454 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08734 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0454 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0203 HalfPureSingletonFanFin10Atom0454 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08735 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0454 χ ∧
      ¬HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0328 HalfPureSingletonFanFin10Atom0454 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08737 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0706 χ ∧
      ¬HalfPureSingletonFanFin10Atom0454 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0454 HalfPureSingletonFanFin10Atom0706 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865, halfPureSingletonFanFin10_cupSet_iff_mask0865] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08749 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0958 χ ∧
      ¬HalfPureSingletonFanFin10Atom0454 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0454 HalfPureSingletonFanFin10Atom0958 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865, halfPureSingletonFanFin10_capSet_iff_mask0865] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08750 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0958 χ ∧
      ¬HalfPureSingletonFanFin10Atom0027 χ ∧
      ¬HalfPureSingletonFanFin10Atom0029 χ ∧
      ¬HalfPureSingletonFanFin10Atom0030 χ ∧
      ¬HalfPureSingletonFanFin10Atom0032 χ ∧
      ¬HalfPureSingletonFanFin10Atom0033 χ ∧
      ¬HalfPureSingletonFanFin10Atom0036 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0113 χ ∧
      ¬HalfPureSingletonFanFin10Atom0116 χ ∧
      ¬HalfPureSingletonFanFin10Atom0119 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0027 HalfPureSingletonFanFin10Atom0029
    HalfPureSingletonFanFin10Atom0030 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0112 HalfPureSingletonFanFin10Atom0113
    HalfPureSingletonFanFin10Atom0116 HalfPureSingletonFanFin10Atom0119
    HalfPureSingletonFanFin10Atom0958 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0865, halfPureSingletonFanFin10_capSet_iff_mask0865] at hbad
  cases hcolor0 : χ ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 6, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08763 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0455 χ ∧
      ¬HalfPureSingletonFanFin10Atom0200 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0455 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0929] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08764 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0455 χ ∧
      ¬HalfPureSingletonFanFin10Atom0204 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0204 HalfPureSingletonFanFin10Atom0455 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0929] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08767 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0707 χ ∧
      ¬HalfPureSingletonFanFin10Atom0455 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0455 HalfPureSingletonFanFin10Atom0707 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0929, halfPureSingletonFanFin10_cupSet_iff_mask0929] at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08779 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0959 χ ∧
      ¬HalfPureSingletonFanFin10Atom0455 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0455 HalfPureSingletonFanFin10Atom0959 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0929, halfPureSingletonFanFin10_capSet_iff_mask0929] at hbad
  cases hcolor0 : χ ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨5, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨5, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨5, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08791 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0456 χ ∧
      ¬HalfPureSingletonFanFin10Atom0201 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0201 HalfPureSingletonFanFin10Atom0456 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0961] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08792 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0456 χ ∧
      ¬HalfPureSingletonFanFin10Atom0202 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0202 HalfPureSingletonFanFin10Atom0456 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0961] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08793 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0456 χ ∧
      ¬HalfPureSingletonFanFin10Atom0203 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0203 HalfPureSingletonFanFin10Atom0456 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0961] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause08797 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0708 χ ∧
      ¬HalfPureSingletonFanFin10Atom0456 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0456 HalfPureSingletonFanFin10Atom0708 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0961, halfPureSingletonFanFin10_cupSet_iff_mask0961] at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08798 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0708 χ ∧
      HalfPureSingletonFanFin10Atom0031 χ ∧
      HalfPureSingletonFanFin10Atom0032 χ ∧
      HalfPureSingletonFanFin10Atom0033 χ ∧
      HalfPureSingletonFanFin10Atom0034 χ ∧
      HalfPureSingletonFanFin10Atom0035 χ ∧
      HalfPureSingletonFanFin10Atom0036 χ ∧
      HalfPureSingletonFanFin10Atom0117 χ ∧
      HalfPureSingletonFanFin10Atom0118 χ ∧
      HalfPureSingletonFanFin10Atom0119 χ ∧
      HalfPureSingletonFanFin10Atom0120 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0031 HalfPureSingletonFanFin10Atom0032
    HalfPureSingletonFanFin10Atom0033 HalfPureSingletonFanFin10Atom0034
    HalfPureSingletonFanFin10Atom0035 HalfPureSingletonFanFin10Atom0036
    HalfPureSingletonFanFin10Atom0117 HalfPureSingletonFanFin10Atom0118
    HalfPureSingletonFanFin10Atom0119 HalfPureSingletonFanFin10Atom0120
    HalfPureSingletonFanFin10Atom0708 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0961, halfPureSingletonFanFin10_cupSet_iff_mask0961] at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause08809 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0960 χ ∧
      ¬HalfPureSingletonFanFin10Atom0456 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0456 HalfPureSingletonFanFin10Atom0960 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0961, halfPureSingletonFanFin10_capSet_iff_mask0961] at hbad
  cases hcolor0 : χ ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨0, 7, 8, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨0, 7, 9, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨0, 8, 9, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨6, 7, 8, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨6, 7, 9, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨6, 8, 9, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨7, 8, 9, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause10921 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0527 χ ∧
      ¬HalfPureSingletonFanFin10Atom0261 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0261 HalfPureSingletonFanFin10Atom0527 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10922 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0527 χ ∧
      ¬HalfPureSingletonFanFin10Atom0262 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0262 HalfPureSingletonFanFin10Atom0527 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10923 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0527 χ ∧
      ¬HalfPureSingletonFanFin10Atom0266 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0527 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10924 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0527 χ ∧
      ¬HalfPureSingletonFanFin10Atom0276 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0276 HalfPureSingletonFanFin10Atom0527 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10925 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0527 χ ∧
      ¬HalfPureSingletonFanFin10Atom0296 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0296 HalfPureSingletonFanFin10Atom0527 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10927 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0779 χ ∧
      ¬HalfPureSingletonFanFin10Atom0527 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0527 HalfPureSingletonFanFin10Atom0779 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124, halfPureSingletonFanFin10_cupSet_iff_mask0124] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause10939 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom1031 χ ∧
      ¬HalfPureSingletonFanFin10Atom0527 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0527 HalfPureSingletonFanFin10Atom1031 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0124, halfPureSingletonFanFin10_capSet_iff_mask0124] at hbad
  cases hcolor0 : χ ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
          cases hcolor4 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
            cases hcolor5 : χ ⟨2, 5, 6, by decide, by decide⟩ <;>
              cases hcolor6 : χ ⟨3, 4, 5, by decide, by decide⟩ <;>
                cases hcolor7 : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
                  cases hcolor8 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
                    cases hcolor9 : χ ⟨4, 5, 6, by decide, by decide⟩ <;>
                      simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause10981 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0529 χ ∧
      ¬HalfPureSingletonFanFin10Atom0261 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0261 HalfPureSingletonFanFin10Atom0529 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316] at hbad
  tauto

theorem halfPureSingletonFanFin10_clause10982 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0529 χ ∧
      ¬HalfPureSingletonFanFin10Atom0264 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0529 at hbad
  simp only [halfPureSingletonFanFin10_strongSet_iff_mask0316] at hbad
  tauto

end ErdosSzekeres

end
