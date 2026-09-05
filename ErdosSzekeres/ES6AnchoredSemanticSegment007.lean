module

public import ErdosSzekeres.ES6AnchoredClauseChunk025
public import ErdosSzekeres.ES6AnchoredClauseChunk026
public import ErdosSzekeres.ES6AnchoredClauseChunk027
public import ErdosSzekeres.ES6AnchoredClauseChunk028
public import ErdosSzekeres.ES6AnchoredClauseChunk029

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 007. -/

theorem es6Anchored_rejectSemanticSegment007
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
    ¬((((((((((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))))))))) ∨
      ((((((((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause03263 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03264 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03265 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03266 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03267 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03268 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03269 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03270 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03271 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03272 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03273 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03274 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03275 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03276 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03277 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03278 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03279 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03280 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03281 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03282 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03283 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03284 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03285 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03286 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03287 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03288 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03289 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03290 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03291 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03292 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03293 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03294 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03295 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03296 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03297 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03298 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03299 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03300 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03301 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03302 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03303 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03304 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03305 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03306 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03307 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03308 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03309 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03310 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03311 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03312 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03313 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03314 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03315 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03316 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03317 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03318 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03319 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03320 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03321 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03322 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03323 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03324 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03325 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03326 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03327 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03328 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03329 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03330 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03331 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03332 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03333 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03334 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03335 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03336 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03337 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03338 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03339 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03340 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03341 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03342 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03343 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03344 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03345 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03346 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03347 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03348 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03349 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03350 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03351 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03352 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03353 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03354 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03355 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03356 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03357 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03358 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03359 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03360 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03361 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03362 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03363 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03364 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03365 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03366 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03367 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03368 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03369 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03370 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03371 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03372 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03373 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03374 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03375 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03376 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03377 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03378 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03379 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03380 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03381 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03382 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03383 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03384 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03385 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03386 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03387 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03388 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03389 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03390 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03391 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03392 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03393 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03394 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03395 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03396 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03397 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03398 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03399 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03400 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03401 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03402 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03403 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03404 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03405 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03406 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03407 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03408 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03409 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03410 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03411 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03412 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03413 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03414 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03415 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03416 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03417 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03418 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03419 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03420 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03421 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03422 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03423 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03424 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03425 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03426 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03427 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03428 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03429 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03430 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03431 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03432 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03433 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03434 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03435 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03436 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03437 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03438 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03439 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03440 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03441 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03442 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03443 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03444 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03445 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03446 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03447 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03448 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03449 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03450 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03451 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03452 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03453 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03454 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03455 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03456 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03457 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03458 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03459 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03460 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03461 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03462 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03463 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03464 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03465 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03466 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03467 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03468 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03469 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03470 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03471 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03472 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03473 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03474 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03475 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03476 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03477 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03478 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03479 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03480 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03481 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03482 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03483 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03484 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03485 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03486 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03487 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03488 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03489 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03490 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03491 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03492 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03493 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03494 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03495 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03496 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03497 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03498 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03499 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03500 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03501 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03502 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03503 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03504 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03505 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03506 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03507 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03508 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03509 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03510 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03511 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03512 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03513 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03514 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03515 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03516 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03517 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03518 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03519 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03520 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03521 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03522 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03523 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03524 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03525 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03526 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03527 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03528 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03529 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03530 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03531 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03532 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03533 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03534 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03535 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03536 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03537 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03538 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03539 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03540 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03541 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03542 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03543 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03544 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03545 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03546 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03547 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03548 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03549 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03550 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03551 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03552 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03553 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03554 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03555 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03556 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03557 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03558 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03559 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03560 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03561 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03562 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03563 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03564 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03565 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03566 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03567 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03568 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03569 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03570 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03571 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03572 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03573 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03574 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03575 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03576 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03577 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03578 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03579 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03580 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03581 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03582 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03583 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03584 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03585 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03586 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03587 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03588 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03589 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03590 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03591 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03592 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03593 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03594 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03595 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03596 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03597 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03598 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03599 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03600 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03601 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03602 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03603 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03604 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03605 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03606 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03607 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03608 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03609 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03610 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03611 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03612 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03613 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03614 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03615 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03616 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03617 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03618 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03619 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03620 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03621 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03622 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03623 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03624 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03625 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03626 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03627 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03628 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03629 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03630 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03631 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03632 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03633 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03634 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03635 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03636 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03637 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03638 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03639 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03640 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03641 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03642 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03643 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03644 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03645 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03646 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03647 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03648 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03649 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03650 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03651 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03652 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03653 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03654 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03655 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03656 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03657 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03658 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03659 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03660 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03661 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03662 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03663 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03664 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03665 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03666 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03667 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03668 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03669 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03670 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03671 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03672 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03673 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03674 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03675 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03676 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03677 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03678 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03679 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03680 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03681 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03682 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03683 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03684 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03685 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03686 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03687 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03688 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03689 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03690 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03691 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03692 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03693 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03694 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03695 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03696 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03697 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03698 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03699 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03700 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03701 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03702 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03703 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03704 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03705 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03706 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03707 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03708 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03709 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03710 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03711 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03712 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03713 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03714 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03715 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03716 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03717 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03718 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03719 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03720 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03721 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03722 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03723 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03724 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03725 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03726 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03727 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03728 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03729 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
