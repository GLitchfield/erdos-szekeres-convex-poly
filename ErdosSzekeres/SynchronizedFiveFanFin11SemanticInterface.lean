module

public import ErdosSzekeres.HalfPureSingletonFan

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-- The exact selected-cube synchronized five-fan conclusion at Fin 11. -/
def SynchronizedFiveFanFin11Conclusion (chi : TripleColoring 11) : Prop :=
  ∃ side : Finset (Fin 11), ∃ pivot : Fin 11,
    pivot ∉ side ∧
    side.card = 6 ∧
    ((HasDeepBelowSplit chi side {pivot} ∧
        ∀ polygon : Finset (Fin 11),
          polygon ⊆ side → polygon.card = 5 →
            IsStrongPolygonSet chi polygon → IsCupSet chi polygon) ∨
     (HasDeepBelowSplit chi {pivot} side ∧
        ∀ polygon : Finset (Fin 11),
          polygon ⊆ side → polygon.card = 5 →
            IsStrongPolygonSet chi polygon → IsCapSet chi polygon))

/-- The six original triple literals of the frozen selected Fin11 cube. -/
def SynchronizedFiveFanFin11SelectedCube (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
    chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
    chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left ∧
    chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right ∧
    chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.right ∧
    chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right

end ErdosSzekeres

end
