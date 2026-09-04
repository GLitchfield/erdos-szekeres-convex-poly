module

public import ErdosSzekeres.ES6AnchoredClauseChunk112
public import ErdosSzekeres.ES6AnchoredClauseChunk113
public import ErdosSzekeres.ES6AnchoredClauseChunk114
public import ErdosSzekeres.ES6AnchoredClauseChunk115
public import ErdosSzekeres.ES6AnchoredClauseChunk116

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 031. -/

theorem es6Anchored_rejectSemanticSegment031
    (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(((((((((((chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left)))))))))) ∨
      ((((((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left)))))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14454 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14455 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14456 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14457 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14458 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14459 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14460 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14461 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14462 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14463 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14464 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14465 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14466 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14467 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14468 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14469 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14470 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14471 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14472 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14473 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14474 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14475 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14476 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14477 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14478 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14479 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14480 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14481 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14482 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14483 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14484 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14485 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14486 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14487 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14488 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14489 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14490 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14491 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14492 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14493 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14494 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14495 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14496 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14497 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14498 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14499 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14500 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14501 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14502 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14503 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14504 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14505 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14506 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14507 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14508 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14509 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14510 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14511 chi hallowed hno hanchor hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14512 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14513 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14514 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14515 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14516 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14517 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14518 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14519 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14520 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14521 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14522 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14523 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14524 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14525 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14526 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14527 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14528 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14529 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14530 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14531 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14532 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14533 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14534 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14535 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14536 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14537 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14538 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14539 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14540 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14541 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14542 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14543 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14544 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14545 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14546 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14547 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14548 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14549 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14550 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14551 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14552 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14553 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14554 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14555 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14556 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14557 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14558 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14559 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14560 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14561 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14562 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14563 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14564 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14565 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14566 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14567 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14568 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14569 chi hallowed hno hanchor hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14570 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14571 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14572 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14573 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14574 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14575 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14576 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14577 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14578 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14579 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14580 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14581 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14582 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14583 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14584 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14585 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14586 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14587 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14588 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14589 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14590 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14591 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14592 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14593 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14594 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14595 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14596 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14597 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14598 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14599 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14600 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14601 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14602 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14603 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14604 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14605 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14606 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14607 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14608 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14609 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14610 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14611 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14612 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14613 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14614 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14615 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14616 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14617 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14618 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14619 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14620 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14621 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14622 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14623 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14624 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14625 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14626 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14627 chi hallowed hno hanchor hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14628 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14629 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14630 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14631 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14632 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14633 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14634 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14635 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14636 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14637 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14638 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14639 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14640 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14641 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14642 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14643 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14644 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14645 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14646 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14647 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14648 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14649 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14650 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14651 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14652 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14653 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14654 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14655 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14656 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14657 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14658 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14659 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14660 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14661 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14662 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14663 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14664 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14665 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14666 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14667 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14668 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14669 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14670 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14671 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14672 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14673 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14674 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14675 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14676 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14677 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14678 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14679 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14680 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14681 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14682 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14683 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14684 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14685 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14686 chi hallowed hno hanchor hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14687 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14688 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14689 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14690 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14691 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14692 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14693 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14694 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14695 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14696 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14697 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14698 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14699 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14700 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14701 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14702 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14703 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14704 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14705 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14706 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14707 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14708 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14709 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14710 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14711 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14712 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14713 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14714 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14715 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14716 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14717 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14718 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14719 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14720 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14721 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14722 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14723 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14724 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14725 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14726 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14727 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14728 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14729 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14730 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14731 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14732 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14733 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14734 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14735 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14736 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14737 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14738 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14739 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14740 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14741 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14742 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14743 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14744 chi hallowed hno hanchor hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14745 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14746 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14747 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14748 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14749 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14750 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14751 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14752 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14753 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14754 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14755 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14756 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14757 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14758 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14759 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14760 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14761 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14762 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14763 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14764 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14765 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14766 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14767 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14768 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14769 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14770 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14771 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14772 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14773 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14774 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14775 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14776 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14777 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14778 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14779 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14780 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14781 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14782 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14783 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14784 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14785 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14786 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14787 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14788 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14789 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14790 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14791 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14792 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14793 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14794 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14795 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14796 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14797 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14798 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14799 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14800 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14801 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14802 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14803 chi hallowed hno hanchor hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14804 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14805 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14806 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14807 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14808 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14809 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14810 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14811 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14812 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14813 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14814 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14815 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14816 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14817 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14818 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14819 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14820 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14821 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14822 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14823 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14824 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14825 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14826 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14827 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14828 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14829 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14830 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14831 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14832 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14833 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14834 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14835 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14836 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14837 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14838 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14839 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14840 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14841 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14842 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14843 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14844 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14845 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14846 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14847 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14848 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14849 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14850 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14851 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14852 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14853 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14854 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14855 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14856 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14857 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14858 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14859 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14860 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14861 chi hallowed hno hanchor hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14862 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14863 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14864 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14865 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14866 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14867 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14868 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14869 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14870 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14871 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14872 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14873 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14874 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14875 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14876 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14877 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14878 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14879 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14880 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14881 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14882 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14883 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14884 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14885 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14886 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14887 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14888 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14889 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14890 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14891 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14892 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14893 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14894 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14895 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14896 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14897 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14898 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14899 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14900 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14901 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14902 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14903 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14904 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14905 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause14906 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14907 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14908 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14909 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14910 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14911 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14912 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14913 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14914 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14915 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14916 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14917 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14918 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause14919 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause14920 chi hallowed hno hanchor hbad

end ErdosSzekeres

end
