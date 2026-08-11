module

public import ErdosSzekeres.ExtremeExchangeK9StrongClause89CNFGenerated
public import ErdosSzekeres.ExtremeExchangeK9StrongClause98CNFGenerated

@[expose] public section

/-! Exact normalized Fin-17 consequences of the two extreme-exchange certificates. -/

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ErdosSzekeres

def ExtremeExchangeK9FinSeventeen89 : Prop :=
  ∀ χ : TripleColoring 17,
    OneChangeOn χ Finset.univ →
      IsCupSet χ {0, 1, 2, 3, 4, 5, 6, 7} →
        IsCupSet χ {8, 9, 10, 11, 12, 13, 14, 15, 16} →
          (∀ f : Fin 4 ↪o Fin 17, ¬ IsCap χ f) →
            (∀ f : Fin 10 ↪o Fin 17, ¬ IsStrongPolygonOn χ f) →
              IsCup χ ExtremeExchangeK9Exchange89First ∨
                IsCup χ ExtremeExchangeK9Exchange89Last

theorem extremeExchangeK9FinSeventeen89 :
    ExtremeExchangeK9FinSeventeen89 := by
  intro χ hone hsmall hbig hnoCap hnoStrong
  by_contra hout
  push Not at hout
  rcases hout with ⟨hnoFirst, hnoLast⟩
  have hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  exact extremeExchangeK9Dense89CNF_unsat χ
    (extremeExchangeK9Dense89CNF_of_constraints χ
      hallowed hnoCap hnoStrong hsmall hbig hnoFirst hnoLast)


def ExtremeExchangeK9FinSeventeen98 : Prop :=
  ∀ χ : TripleColoring 17,
    OneChangeOn χ Finset.univ →
      IsCupSet χ {9, 10, 11, 12, 13, 14, 15, 16} →
        IsCupSet χ {0, 1, 2, 3, 4, 5, 6, 7, 8} →
          (∀ f : Fin 4 ↪o Fin 17, ¬ IsCap χ f) →
            (∀ f : Fin 10 ↪o Fin 17, ¬ IsStrongPolygonOn χ f) →
              IsCup χ ExtremeExchangeK9Exchange98First ∨
                IsCup χ ExtremeExchangeK9Exchange98Last

theorem extremeExchangeK9FinSeventeen98 :
    ExtremeExchangeK9FinSeventeen98 := by
  intro χ hone hsmall hbig hnoCap hnoStrong
  by_contra hout
  push Not at hout
  rcases hout with ⟨hnoFirst, hnoLast⟩
  have hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  exact extremeExchangeK9Dense98CNF_unsat χ
    (extremeExchangeK9Dense98CNF_of_constraints χ
      hallowed hnoCap hnoStrong hsmall hbig hnoFirst hnoLast)


theorem extremeExchangeK9FinSeventeen :
    ExtremeExchangeK9FinSeventeen89 ∧ ExtremeExchangeK9FinSeventeen98 := by
  exact ⟨extremeExchangeK9FinSeventeen89, extremeExchangeK9FinSeventeen98⟩

end ErdosSzekeres

end
