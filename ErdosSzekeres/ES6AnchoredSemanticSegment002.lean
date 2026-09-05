module

public import ErdosSzekeres.ES6AnchoredClauseChunk007
public import ErdosSzekeres.ES6AnchoredClauseChunk008
public import ErdosSzekeres.ES6AnchoredClauseChunk009
public import ErdosSzekeres.ES6AnchoredClauseChunk010

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 002. -/

theorem es6Anchored_rejectSemanticSegment002
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
    ¬(((((((((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)))))))))) ∨
      (((((((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause00932 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00933 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00934 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00935 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00936 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00937 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00938 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause00939 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00940 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00941 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00942 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00943 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00944 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00945 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause00946 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00947 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00948 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00949 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00950 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00951 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00952 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00953 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00954 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00955 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00956 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00957 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00958 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00959 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00960 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause00961 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00962 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00963 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00964 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00965 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00966 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00967 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause00968 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00969 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00970 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00971 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00972 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00973 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00974 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause00975 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00976 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00977 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00978 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00979 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00980 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00981 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00982 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00983 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00984 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00985 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00986 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00987 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00988 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00989 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause00990 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00991 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00992 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00993 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00994 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00995 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00996 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause00997 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause00998 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause00999 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01000 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01001 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01002 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01003 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01004 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01005 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01006 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01007 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01008 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01009 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01010 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01011 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01012 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01013 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01014 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01015 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01016 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01017 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01018 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01019 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01020 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01021 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01022 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01023 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01024 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01025 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01026 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01027 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01028 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01029 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01030 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01031 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01032 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01033 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01034 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01035 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01036 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01037 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01038 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01039 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01040 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01041 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01042 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01043 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01044 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01045 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01046 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01047 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause01048 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01049 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01050 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01051 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01052 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01053 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01054 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01055 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01056 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01057 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01058 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01059 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01060 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01061 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01062 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01063 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01064 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01065 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01066 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01067 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01068 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01069 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01070 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01071 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01072 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01073 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01074 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01075 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01076 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01077 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01078 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01079 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01080 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01081 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01082 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01083 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01084 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01085 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01086 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01087 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01088 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01089 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01090 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01091 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01092 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01093 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01094 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01095 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01096 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01097 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01098 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01099 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01100 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01101 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01102 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01103 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01104 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01105 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause01106 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01107 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01108 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01109 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01110 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01111 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01112 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01113 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01114 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01115 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01116 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01117 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01118 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01119 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01120 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01121 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01122 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01123 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01124 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01125 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01126 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01127 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01128 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01129 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01130 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01131 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01132 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01133 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01134 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01135 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01136 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01137 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01138 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01139 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01140 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01141 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01142 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01143 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01144 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01145 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01146 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01147 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01148 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01149 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01150 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01151 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01152 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01153 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01154 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01155 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01156 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01157 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01158 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01159 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01160 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01161 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01162 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01163 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01164 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause01165 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01166 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01167 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01168 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01169 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01170 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01171 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01172 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01173 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01174 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01175 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01176 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01177 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01178 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01179 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01180 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01181 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01182 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01183 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01184 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01185 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01186 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01187 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01188 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01189 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01190 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01191 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01192 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01193 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01194 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01195 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01196 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01197 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01198 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01199 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01200 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01201 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01202 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01203 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01204 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01205 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01206 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01207 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01208 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01209 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01210 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01211 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01212 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01213 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01214 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01215 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01216 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01217 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01218 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01219 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01220 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01221 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01222 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause01223 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01224 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01225 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01226 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01227 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01228 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01229 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01230 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01231 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01232 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01233 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01234 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01235 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01236 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01237 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01238 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01239 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01240 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01241 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01242 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01243 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01244 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01245 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01246 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01247 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01248 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01249 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01250 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01251 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01252 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01253 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01254 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01255 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01256 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01257 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01258 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01259 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01260 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01261 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01262 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01263 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01264 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01265 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01266 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01267 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01268 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01269 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01270 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01271 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01272 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01273 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01274 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01275 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01276 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01277 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01278 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01279 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01280 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause01281 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01282 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01283 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01284 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01285 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01286 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01287 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01288 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01289 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01290 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01291 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01292 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01293 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01294 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01295 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01296 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01297 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01298 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01299 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01300 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01301 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01302 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01303 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01304 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01305 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01306 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01307 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01308 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01309 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01310 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01311 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01312 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01313 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01314 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01315 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01316 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01317 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01318 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01319 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01320 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01321 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01322 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01323 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01324 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01325 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01326 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01327 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01328 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01329 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01330 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01331 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01332 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01333 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01334 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01335 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01336 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01337 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01338 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause01339 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01340 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01341 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01342 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01343 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01344 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01345 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01346 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01347 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01348 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01349 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01350 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01351 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01352 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01353 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01354 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01355 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01356 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01357 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01358 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01359 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01360 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01361 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01362 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01363 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01364 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01365 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01366 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01367 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01368 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01369 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01370 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01371 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01372 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01373 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01374 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01375 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01376 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01377 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01378 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01379 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01380 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01381 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01382 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause01383 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01384 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01385 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01386 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01387 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01388 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01389 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01390 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01391 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01392 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01393 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01394 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01395 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause01396 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause01397 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
