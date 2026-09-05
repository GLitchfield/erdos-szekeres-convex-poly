module

public import ErdosSzekeres.ES6AnchoredClauseChunk138
public import ErdosSzekeres.ES6AnchoredClauseChunk139
public import ErdosSzekeres.ES6AnchoredClauseChunk140
public import ErdosSzekeres.ES6AnchoredClauseChunk141
public import ErdosSzekeres.ES6AnchoredClauseChunk142

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 038. -/

theorem es6Anchored_rejectSemanticSegment038
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
    ¬((((((((((¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left)))))))))) ∨
      ((((((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨0, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause17718 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17719 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17720 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17721 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17722 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17723 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17724 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17725 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17726 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17727 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17728 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17729 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17730 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17731 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17732 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17733 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17734 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17735 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17736 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17737 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17738 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17739 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17740 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17741 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17742 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17743 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17744 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17745 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17746 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17747 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17748 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17749 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17750 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17751 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17752 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17753 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17754 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17755 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17756 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17757 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17758 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17759 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17760 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17761 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17762 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17763 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17764 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17765 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17766 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17767 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17768 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17769 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17770 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17771 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17772 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17773 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17774 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17775 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause17776 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17777 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17778 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17779 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17780 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17781 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17782 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17783 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17784 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17785 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17786 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17787 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17788 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17789 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17790 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17791 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17792 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17793 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17794 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17795 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17796 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17797 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17798 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17799 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17800 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17801 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17802 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17803 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17804 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17805 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17806 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17807 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17808 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17809 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17810 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17811 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17812 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17813 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17814 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17815 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17816 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17817 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17818 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17819 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17820 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17821 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17822 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17823 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17824 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17825 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17826 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17827 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17828 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17829 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17830 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17831 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17832 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17833 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause17834 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17835 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17836 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17837 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17838 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17839 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17840 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17841 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17842 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17843 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17844 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17845 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17846 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17847 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17848 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17849 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17850 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17851 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17852 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17853 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17854 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17855 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17856 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17857 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17858 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17859 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17860 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17861 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17862 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17863 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17864 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17865 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17866 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17867 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17868 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17869 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17870 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17871 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17872 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17873 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17874 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17875 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17876 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17877 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17878 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17879 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17880 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17881 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17882 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17883 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17884 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17885 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17886 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17887 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17888 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17889 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17890 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17891 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause17892 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17893 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17894 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17895 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17896 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17897 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17898 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17899 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17900 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17901 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17902 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17903 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17904 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17905 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17906 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17907 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17908 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17909 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17910 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17911 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17912 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17913 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17914 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17915 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17916 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17917 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17918 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17919 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17920 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17921 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17922 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17923 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17924 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17925 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17926 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17927 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17928 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17929 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17930 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17931 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17932 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17933 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17934 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17935 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17936 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17937 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17938 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17939 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17940 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17941 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17942 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17943 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17944 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17945 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17946 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17947 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17948 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17949 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17950 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause17951 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17952 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17953 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17954 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17955 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17956 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17957 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17958 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17959 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17960 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17961 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17962 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17963 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17964 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17965 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17966 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17967 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17968 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17969 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17970 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17971 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17972 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17973 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17974 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17975 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17976 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17977 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17978 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17979 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17980 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17981 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17982 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17983 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17984 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17985 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17986 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17987 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17988 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17989 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17990 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17991 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17992 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17993 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause17994 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17995 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17996 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17997 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause17998 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause17999 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18000 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18001 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18002 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18003 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18004 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18005 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18006 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18007 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18008 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause18009 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18010 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18011 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18012 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18013 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18014 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18015 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18016 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18017 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18018 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18019 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18020 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18021 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18022 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18023 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18024 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18025 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18026 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18027 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18028 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18029 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18030 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18031 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18032 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18033 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18034 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18035 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18036 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18037 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18038 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18039 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18040 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18041 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18042 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18043 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18044 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18045 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18046 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18047 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18048 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18049 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18050 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18051 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18052 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18053 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18054 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18055 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18056 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18057 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18058 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18059 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18060 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18061 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18062 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18063 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18064 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18065 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18066 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause18067 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18068 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18069 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18070 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18071 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18072 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18073 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18074 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18075 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18076 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18077 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18078 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18079 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18080 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18081 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18082 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18083 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18084 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18085 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18086 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18087 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18088 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18089 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18090 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18091 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18092 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18093 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18094 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18095 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18096 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18097 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18098 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18099 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18100 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18101 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18102 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18103 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18104 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18105 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18106 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18107 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18108 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18109 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18110 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18111 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18112 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18113 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18114 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18115 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18116 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18117 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18118 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18119 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18120 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18121 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18122 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18123 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18124 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause18125 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18126 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18127 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18128 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18129 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18130 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18131 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18132 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18133 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18134 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18135 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18136 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18137 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18138 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18139 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18140 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18141 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18142 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18143 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18144 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18145 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18146 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18147 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18148 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18149 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18150 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18151 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18152 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18153 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18154 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18155 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18156 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18157 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18158 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18159 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18160 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18161 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18162 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18163 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18164 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18165 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18166 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18167 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18168 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause18169 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18170 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18171 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18172 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18173 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18174 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18175 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18176 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18177 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18178 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18179 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18180 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18181 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause18182 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause18183 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
