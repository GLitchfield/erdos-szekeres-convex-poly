module

public import ErdosSzekeres.ES6AnchoredClauseChunk021
public import ErdosSzekeres.ES6AnchoredClauseChunk022
public import ErdosSzekeres.ES6AnchoredClauseChunk023
public import ErdosSzekeres.ES6AnchoredClauseChunk024
public import ErdosSzekeres.ES6AnchoredClauseChunk025

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 006. -/

theorem es6Anchored_rejectSemanticSegment006
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
    ¬(((((((((((chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)))))))))) ∨
      (((((((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause02797 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02798 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02799 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02800 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02801 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02802 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02803 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02804 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02805 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02806 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02807 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02808 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02809 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02810 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02811 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02812 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02813 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02814 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02815 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02816 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02817 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02818 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02819 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02820 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02821 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02822 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02823 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02824 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02825 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02826 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02827 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02828 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02829 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02830 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02831 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02832 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02833 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02834 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02835 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02836 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02837 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02838 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02839 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02840 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02841 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02842 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02843 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02844 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02845 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02846 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02847 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02848 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02849 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02850 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02851 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02852 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02853 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02854 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause02855 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02856 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02857 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02858 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02859 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02860 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02861 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02862 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02863 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02864 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02865 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02866 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02867 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02868 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02869 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02870 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02871 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02872 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02873 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02874 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02875 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02876 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02877 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02878 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02879 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02880 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02881 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02882 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02883 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02884 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02885 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02886 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02887 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02888 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02889 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02890 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02891 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02892 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02893 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02894 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02895 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02896 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02897 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02898 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02899 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02900 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02901 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02902 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02903 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02904 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02905 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02906 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02907 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02908 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02909 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02910 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02911 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02912 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause02913 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02914 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02915 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02916 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02917 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02918 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02919 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02920 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02921 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02922 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02923 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02924 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02925 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02926 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02927 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02928 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02929 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02930 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02931 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02932 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02933 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02934 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02935 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02936 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02937 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02938 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02939 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02940 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02941 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02942 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02943 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02944 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02945 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02946 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02947 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02948 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02949 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02950 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02951 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02952 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02953 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02954 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02955 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02956 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02957 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02958 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02959 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02960 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02961 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02962 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02963 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02964 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02965 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02966 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02967 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02968 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02969 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02970 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause02971 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02972 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02973 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02974 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02975 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02976 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02977 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02978 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02979 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02980 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02981 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02982 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02983 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02984 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause02985 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02986 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02987 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02988 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02989 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02990 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02991 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02992 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02993 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02994 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02995 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02996 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02997 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause02998 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause02999 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03000 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03001 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03002 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03003 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03004 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03005 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03006 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03007 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03008 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03009 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03010 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03011 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03012 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03013 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03014 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03015 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03016 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03017 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03018 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03019 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03020 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03021 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03022 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03023 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03024 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03025 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03026 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03027 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03028 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03029 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03030 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03031 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03032 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03033 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03034 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03035 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03036 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03037 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03038 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03039 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03040 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03041 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03042 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03043 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03044 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03045 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03046 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03047 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03048 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03049 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03050 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03051 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03052 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03053 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03054 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03055 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03056 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03057 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03058 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03059 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03060 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03061 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03062 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03063 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03064 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03065 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03066 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03067 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03068 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03069 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03070 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03071 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03072 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03073 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03074 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03075 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03076 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03077 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03078 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03079 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03080 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03081 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03082 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03083 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03084 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03085 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03086 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03087 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03088 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03089 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03090 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03091 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03092 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03093 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03094 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03095 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03096 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03097 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03098 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03099 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03100 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03101 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03102 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03103 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03104 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03105 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03106 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03107 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03108 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03109 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03110 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03111 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03112 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03113 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03114 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03115 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03116 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03117 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03118 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03119 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03120 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03121 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03122 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03123 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03124 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03125 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03126 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03127 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03128 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03129 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03130 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03131 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03132 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03133 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03134 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03135 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03136 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03137 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03138 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03139 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03140 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03141 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03142 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03143 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03144 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03145 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03146 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03147 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03148 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03149 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03150 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03151 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03152 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03153 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03154 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03155 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03156 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03157 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03158 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03159 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03160 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03161 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03162 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03163 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03164 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03165 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03166 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03167 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03168 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03169 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03170 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03171 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03172 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03173 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03174 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03175 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03176 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03177 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03178 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03179 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03180 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03181 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03182 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03183 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03184 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03185 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03186 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03187 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03188 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03189 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03190 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03191 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03192 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03193 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03194 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03195 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03196 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03197 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03198 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03199 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03200 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03201 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03202 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03203 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause03204 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03205 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03206 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03207 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03208 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03209 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03210 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03211 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03212 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03213 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03214 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03215 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03216 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03217 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03218 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03219 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03220 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03221 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03222 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03223 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03224 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03225 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03226 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03227 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03228 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03229 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03230 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03231 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03232 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03233 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03234 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03235 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03236 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03237 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03238 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03239 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03240 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03241 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03242 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03243 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03244 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03245 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03246 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03247 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause03248 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03249 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03250 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03251 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03252 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03253 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03254 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03255 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03256 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03257 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03258 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03259 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03260 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause03261 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause03262 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
