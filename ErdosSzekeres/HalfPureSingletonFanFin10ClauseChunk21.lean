module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 21. -/

theorem halfPureSingletonFanFin10_clause03772 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03773 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03774 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03775 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03776 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03778 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0278 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03784 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0278 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03785 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0278 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03789 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      ¬HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0278 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03791 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0078 χ ∧
      ¬HalfPureSingletonFanFin10Atom0103 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0078 HalfPureSingletonFanFin10Atom0103
    HalfPureSingletonFanFin10Atom0278 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03793 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03796 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03797 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      ¬HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03798 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03799 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03803 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0279 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0279 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03812 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      ¬HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0279 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0279 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03815 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0071 χ ∧
      HalfPureSingletonFanFin10Atom0075 χ ∧
      HalfPureSingletonFanFin10Atom0079 χ ∧
      ¬HalfPureSingletonFanFin10Atom0104 χ ∧
      HalfPureSingletonFanFin10Atom0279 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0071 HalfPureSingletonFanFin10Atom0075
    HalfPureSingletonFanFin10Atom0079 HalfPureSingletonFanFin10Atom0104
    HalfPureSingletonFanFin10Atom0279 at hbad
  cases hcolor0 : χ ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03818 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03819 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03820 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03821 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03823 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03824 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      ¬HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03832 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0280 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0280 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03839 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      ¬HalfPureSingletonFanFin10Atom0105 χ ∧
      HalfPureSingletonFanFin10Atom0280 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0280 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03840 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0073 χ ∧
      HalfPureSingletonFanFin10Atom0080 χ ∧
      HalfPureSingletonFanFin10Atom0105 χ ∧
      ¬HalfPureSingletonFanFin10Atom0280 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0073
    HalfPureSingletonFanFin10Atom0080 HalfPureSingletonFanFin10Atom0105
    HalfPureSingletonFanFin10Atom0280 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03841 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03842 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03843 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03844 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0072 χ ∧
      HalfPureSingletonFanFin10Atom0074 χ ∧
      HalfPureSingletonFanFin10Atom0081 χ ∧
      ¬HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause03845 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0072 χ ∧
      ¬HalfPureSingletonFanFin10Atom0074 χ ∧
      ¬HalfPureSingletonFanFin10Atom0081 χ ∧
      HalfPureSingletonFanFin10Atom0106 χ) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0072 HalfPureSingletonFanFin10Atom0074
    HalfPureSingletonFanFin10Atom0081 HalfPureSingletonFanFin10Atom0106 at hbad
  cases hcolor0 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
