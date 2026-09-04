module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 086. -/

theorem fin15Anchored_clause11008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11009 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11010 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11011 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1257 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11020 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11023 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1258 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11029 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11031 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11032 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1259 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11038 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11042 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11043 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1260 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11050 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11051 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11052 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1261 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11059 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11062 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1262 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11071 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1263 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11077 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11078 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1264 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1265 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1265 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1265 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1265 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1266 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11087 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1266 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1266 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1266 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1266 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1266 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11095 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1267 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1268 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1269 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1270 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1270 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1270 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11126 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11127 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1271 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1273 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0212 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1273 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1274 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1274 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1274 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1274 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1275 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0214 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1275 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
