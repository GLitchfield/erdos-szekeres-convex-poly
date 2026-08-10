module

public import ErdosSzekeres.DecompositionPrime

@[expose] public section

/-!
# Crossing deep-below splits

Four nonempty corners of two deep-below splits force a strong four-set. This
is the exact unconditional uncrossing consequence; obtaining a larger target
requires additional cup/cap capacity.
-/

namespace ErdosSzekeres

/-- Four nonempty corners of two deep-below splits supply two vertices in
each side of the first split and hence a strong four-set. -/
theorem crossingDeepSplits_containStrongFour
    {n : ℕ} {χ : TripleColoring n}
    {lower₁ upper₁ lower₂ upper₂ : Finset (Fin n)}
    (h₁ : HasDeepBelowSplit χ lower₁ upper₁)
    (h₂ : HasDeepBelowSplit χ lower₂ upper₂)
    {xLL xLU xUL xUU : Fin n}
    (hxLL₁ : xLL ∈ lower₁) (hxLL₂ : xLL ∈ lower₂)
    (hxLU₁ : xLU ∈ lower₁) (hxLU₂ : xLU ∈ upper₂)
    (hxUL₁ : xUL ∈ upper₁) (hxUL₂ : xUL ∈ lower₂)
    (hxUU₁ : xUU ∈ upper₁) (hxUU₂ : xUU ∈ upper₂) :
    ContainsStrongPolygonSet χ (lower₁ ∪ upper₁) 4 := by
  have hLLneLU : xLL ≠ xLU := by
    intro heq
    subst xLU
    exact (Finset.disjoint_left.mp h₂.disjoint) hxLL₂ hxLU₂
  have hULneUU : xUL ≠ xUU := by
    intro heq
    subst xUU
    exact (Finset.disjoint_left.mp h₂.disjoint) hxUL₂ hxUU₂
  have hcupSub : ({xLL, xLU} : Finset (Fin n)) ⊆ lower₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hxLL₁
    · exact hxLU₁
  have hcapSub : ({xUL, xUU} : Finset (Fin n)) ⊆ upper₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hxUL₁
    · exact hxUU₁
  have hcup : IsCupSet χ {xLL, xLU} := by
    intro t hi hj hk
    have hij : t.i ≠ t.j := ne_of_lt t.hij
    have hjk : t.j ≠ t.k := ne_of_lt t.hjk
    have hik : t.i ≠ t.k := ne_of_lt (t.hij.trans t.hjk)
    have hthreeCard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [hij, hjk, hik]
    have hthreeSub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ {xLL, xLU} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have hle := Finset.card_le_card hthreeSub
    have htwoCard : ({xLL, xLU} : Finset (Fin n)).card = 2 := by
      simp [hLLneLU]
    omega
  have hcap : IsCapSet χ {xUL, xUU} := by
    intro t hi hj hk
    have hij : t.i ≠ t.j := ne_of_lt t.hij
    have hjk : t.j ≠ t.k := ne_of_lt t.hjk
    have hik : t.i ≠ t.k := ne_of_lt (t.hij.trans t.hjk)
    have hthreeCard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [hij, hjk, hik]
    have hthreeSub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ {xUL, xUU} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have hle := Finset.card_le_card hthreeSub
    have htwoCard : ({xUL, xUU} : Finset (Fin n)).card = 2 := by
      simp [hULneUU]
    omega
  apply h₁.containsStrongPolygonSet_of_cup_cap hcupSub hcapSub hcup hcap
  simp [hLLneLU, hULneUU]

end ErdosSzekeres

end
