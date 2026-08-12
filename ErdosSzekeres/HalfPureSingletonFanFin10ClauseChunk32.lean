module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 32. -/

theorem halfPureSingletonFanFin10_clause04423 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04424 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04426 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0305 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04433 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      ¬HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0305 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04437 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      ¬HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      ¬HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0305 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04439 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0089 χ ∧
      HalfPureSingletonFanFin10Atom0090 χ ∧
      HalfPureSingletonFanFin10Atom0100 χ ∧
      ¬HalfPureSingletonFanFin10Atom0110 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0089 HalfPureSingletonFanFin10Atom0090
    HalfPureSingletonFanFin10Atom0100 HalfPureSingletonFanFin10Atom0110
    HalfPureSingletonFanFin10Atom0305 at hbad
  cases hcolor0 : χ ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04441 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04442 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04443 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04444 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04445 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04446 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04447 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04448 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04449 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04456 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04457 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04458 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04461 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04462 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      ¬HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04463 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      ¬HalfPureSingletonFanFin10Atom0111 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04464 (χ : TripleColoring 10)
    : ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0092 χ ∧
      HalfPureSingletonFanFin10Atom0095 χ ∧
      HalfPureSingletonFanFin10Atom0111 χ ∧
      ¬HalfPureSingletonFanFin10Atom0306 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0092
    HalfPureSingletonFanFin10Atom0095 HalfPureSingletonFanFin10Atom0111
    HalfPureSingletonFanFin10Atom0306 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04465 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04466 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04467 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04468 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04469 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04470 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04471 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04472 (χ : TripleColoring 10)
    (hone : OneChangeOn χ Finset.univ) :
    ¬(HalfPureSingletonFanFin10Atom0091 χ ∧
      HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04473 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      ¬HalfPureSingletonFanFin10Atom0112 χ ∧
      ¬HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause04474 (χ : TripleColoring 10)
    : ¬(¬HalfPureSingletonFanFin10Atom0091 χ ∧
      ¬HalfPureSingletonFanFin10Atom0093 χ ∧
      ¬HalfPureSingletonFanFin10Atom0096 χ ∧
      HalfPureSingletonFanFin10Atom0112 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ) := by
  intro hbad
  unfold HalfPureSingletonFanFin10Atom0091 HalfPureSingletonFanFin10Atom0093
    HalfPureSingletonFanFin10Atom0096 HalfPureSingletonFanFin10Atom0112
    HalfPureSingletonFanFin10Atom0307 at hbad
  cases hcolor0 : χ ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : χ ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : χ ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : χ ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
