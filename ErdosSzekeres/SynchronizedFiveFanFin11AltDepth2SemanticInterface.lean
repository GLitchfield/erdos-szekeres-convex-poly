module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface
public import ErdosSzekeres.SynchronizedFiveFanFin11BranchInterface

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-- The two frozen alternate-depth-two Boolean positions. -/
abbrev Fin11AltDepth2Assignment := Fin 2 → Bool

/-- Geometric meaning of the two frozen Boolean positions. -/
def Fin11AltDepth2Holds
    (sigma : Fin11AltDepth2Assignment) (chi : TripleColoring 11) : Prop :=
  (chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ↔ sigma 0 = true) ∧
    (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ↔ sigma 1 = true)

theorem fin11AltDepth2Holds_position0
    {sigma : Fin11AltDepth2Assignment} {chi : TripleColoring 11}
    (h : Fin11AltDepth2Holds sigma chi) :
    chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ↔ sigma 0 = true := h.1

theorem fin11AltDepth2Holds_position1
    {sigma : Fin11AltDepth2Assignment} {chi : TripleColoring 11}
    (h : Fin11AltDepth2Holds sigma chi) :
    chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ↔ sigma 1 = true := h.2

end ErdosSzekeres

end
