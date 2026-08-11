module

public import ErdosSzekeres.DiagonalCupBlocksK9Dense78CNFGenerated
public import ErdosSzekeres.DiagonalCupBlocksK9Dense87CNFGenerated

@[expose] public section

/-! Normalized semantic consequences of the two dense k=9 LRAT cores. -/

set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace ErdosSzekeres

theorem diagonalCupBlocksK9_containsCapSet_univ_of_finFour {n : ℕ} {χ : TripleColoring n}
    {f : Fin 4 ↪o Fin n} (h : IsCap χ f) :
    ContainsCapSet χ Finset.univ 4 := by
  refine ⟨Finset.univ.image f, by simp, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ f.injective
  · exact FinsetPolygon.IsCap.image h

theorem diagonalCupBlocksK9_containsCupSet_univ_of_finNine {n : ℕ} {χ : TripleColoring n}
    {f : Fin 9 ↪o Fin n} (h : IsCup χ f) :
    ContainsCupSet χ Finset.univ 9 := by
  refine ⟨Finset.univ.image f, by simp, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ f.injective
  · exact FinsetPolygon.IsCup.image h

theorem diagonalCupBlocksK9_containsStrongPolygonSet_univ_of_finNine {n : ℕ} {χ : TripleColoring n}
    {f : Fin 9 ↪o Fin n} (h : IsStrongPolygonOn χ f) :
    ContainsStrongPolygonSet χ Finset.univ 9 := by
  refine ⟨Finset.univ.image f, by simp, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ f.injective
  · exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h

def DiagonalCupBlocksK9FinFifteen78 : Prop :=
  ∀ χ : TripleColoring 15,
    IsCupSet χ {0, 1, 2, 3, 4, 5, 6} →
      IsCupSet χ {7, 8, 9, 10, 11, 12, 13, 14} →
        OneChangeOn χ Finset.univ →
          ContainsCapSet χ Finset.univ 4 ∨
            ContainsCupSet χ Finset.univ 9 ∨
              ContainsStrongPolygonSet χ Finset.univ 9

theorem diagonalCupBlocksK9FinFifteen78 :
    DiagonalCupBlocksK9FinFifteen78 := by
  intro χ hleft hright hone
  by_contra hout
  have hnoCapSet : ¬ ContainsCapSet χ Finset.univ 4 :=
    fun hcap ↦ hout (Or.inl hcap)
  have hnoCupSet : ¬ ContainsCupSet χ Finset.univ 9 :=
    fun hcup ↦ hout (Or.inr (Or.inl hcup))
  have hnoStrongSet : ¬ ContainsStrongPolygonSet χ Finset.univ 9 :=
    fun hstrong ↦ hout (Or.inr (Or.inr hstrong))
  have hnoCap : ∀ f : Fin 4 ↪o Fin 15, ¬ IsCap χ f := by
    intro f hcap
    exact hnoCapSet (diagonalCupBlocksK9_containsCapSet_univ_of_finFour hcap)
  have hnoCup : ∀ f : Fin 9 ↪o Fin 15, ¬ IsCup χ f := by
    intro f hcup
    exact hnoCupSet (diagonalCupBlocksK9_containsCupSet_univ_of_finNine hcup)
  have hnoStrong : ∀ f : Fin 9 ↪o Fin 15, ¬ IsStrongPolygonOn χ f := by
    intro f hstrong
    exact hnoStrongSet
      (diagonalCupBlocksK9_containsStrongPolygonSet_univ_of_finNine hstrong)
  have hallowed : ∀ (a b c d : Fin 15),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  exact diagonalCupBlocksK9Dense78CNF_unsat χ
    (diagonalCupBlocksK9Dense78CNF_of_constraints χ
      hallowed hnoCap hnoCup hnoStrong hleft hright)

def DiagonalCupBlocksK9FinFifteen87 : Prop :=
  ∀ χ : TripleColoring 15,
    IsCupSet χ {0, 1, 2, 3, 4, 5, 6, 7} →
      IsCupSet χ {8, 9, 10, 11, 12, 13, 14} →
        OneChangeOn χ Finset.univ →
          ContainsCapSet χ Finset.univ 4 ∨
            ContainsCupSet χ Finset.univ 9 ∨
              ContainsStrongPolygonSet χ Finset.univ 9

theorem diagonalCupBlocksK9FinFifteen87 :
    DiagonalCupBlocksK9FinFifteen87 := by
  intro χ hleft hright hone
  by_contra hout
  have hnoCapSet : ¬ ContainsCapSet χ Finset.univ 4 :=
    fun hcap ↦ hout (Or.inl hcap)
  have hnoCupSet : ¬ ContainsCupSet χ Finset.univ 9 :=
    fun hcup ↦ hout (Or.inr (Or.inl hcup))
  have hnoStrongSet : ¬ ContainsStrongPolygonSet χ Finset.univ 9 :=
    fun hstrong ↦ hout (Or.inr (Or.inr hstrong))
  have hnoCap : ∀ f : Fin 4 ↪o Fin 15, ¬ IsCap χ f := by
    intro f hcap
    exact hnoCapSet (diagonalCupBlocksK9_containsCapSet_univ_of_finFour hcap)
  have hnoCup : ∀ f : Fin 9 ↪o Fin 15, ¬ IsCup χ f := by
    intro f hcup
    exact hnoCupSet (diagonalCupBlocksK9_containsCupSet_univ_of_finNine hcup)
  have hnoStrong : ∀ f : Fin 9 ↪o Fin 15, ¬ IsStrongPolygonOn χ f := by
    intro f hstrong
    exact hnoStrongSet
      (diagonalCupBlocksK9_containsStrongPolygonSet_univ_of_finNine hstrong)
  have hallowed : ∀ (a b c d : Fin 15),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  exact diagonalCupBlocksK9Dense87CNF_unsat χ
    (diagonalCupBlocksK9Dense87CNF_of_constraints χ
      hallowed hnoCap hnoCup hnoStrong hleft hright)

end ErdosSzekeres

end
