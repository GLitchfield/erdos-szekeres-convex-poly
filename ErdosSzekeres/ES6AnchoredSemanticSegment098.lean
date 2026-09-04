module

public import ErdosSzekeres.ES6AnchoredClauseChunk356
public import ErdosSzekeres.ES6AnchoredClauseChunk357
public import ErdosSzekeres.ES6AnchoredClauseChunk358
public import ErdosSzekeres.ES6AnchoredClauseChunk359
public import ErdosSzekeres.ES6AnchoredClauseChunk360

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 098. -/

theorem es6Anchored_rejectSemanticSegment098
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
    ¬((((((((((¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))))))) ∨
      (((((((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause45695 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45696 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45697 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45698 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45699 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45700 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45701 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45702 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45703 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45704 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45705 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45706 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45707 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45708 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45709 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45710 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45711 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45712 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45713 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45714 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45715 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45716 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45717 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45718 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45719 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45720 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45721 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45722 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45723 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45724 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45725 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45726 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45727 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45728 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45729 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45730 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45731 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45732 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45733 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45734 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45735 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45736 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45737 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45738 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45739 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45740 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45741 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45742 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45743 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45744 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45745 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45746 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45747 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45748 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45749 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45750 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45751 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45752 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause45753 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45754 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45755 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45756 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45757 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45758 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45759 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45760 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45761 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45762 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45763 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45764 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45765 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45766 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45767 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45768 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45769 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45770 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45771 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45772 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45773 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45774 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45775 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45776 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45777 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45778 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45779 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45780 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45781 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45782 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45783 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45784 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45785 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45786 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45787 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45788 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45789 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45790 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45791 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45792 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45793 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45794 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45795 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45796 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45797 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45798 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45799 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45800 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45801 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45802 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45803 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45804 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45805 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45806 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45807 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45808 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45809 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45810 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause45811 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45812 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45813 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45814 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45815 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45816 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45817 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45818 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45819 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45820 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45821 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45822 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45823 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45824 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45825 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45826 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45827 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45828 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45829 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45830 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45831 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45832 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45833 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45834 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45835 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45836 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45837 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45838 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45839 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45840 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45841 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45842 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45843 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45844 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45845 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45846 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45847 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45848 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45849 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45850 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45851 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45852 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45853 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45854 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45855 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45856 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45857 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45858 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45859 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45860 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45861 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45862 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45863 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45864 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45865 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45866 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45867 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45868 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause45869 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45870 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45871 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45872 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45873 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45874 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45875 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45876 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45877 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45878 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45879 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45880 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45881 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45882 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45883 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45884 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45885 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45886 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45887 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45888 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45889 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45890 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45891 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45892 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45893 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45894 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45895 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45896 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45897 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45898 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45899 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45900 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45901 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45902 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45903 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45904 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45905 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45906 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45907 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45908 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45909 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45910 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45911 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45912 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45913 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45914 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45915 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45916 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45917 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45918 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45919 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45920 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45921 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45922 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45923 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45924 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45925 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45926 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45927 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause45928 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45929 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45930 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45931 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45932 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45933 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45934 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45935 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45936 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45937 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45938 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45939 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45940 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45941 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45942 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45943 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45944 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45945 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45946 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45947 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45948 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45949 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45950 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45951 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45952 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45953 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45954 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45955 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45956 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45957 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45958 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45959 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45960 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45961 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45962 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45963 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45964 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45965 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45966 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45967 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45968 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45969 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45970 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45971 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45972 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45973 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45974 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45975 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45976 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45977 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45978 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45979 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45980 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45981 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45982 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45983 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45984 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45985 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause45986 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45987 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45988 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45989 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45990 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45991 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45992 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause45993 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45994 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45995 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45996 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45997 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause45998 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause45999 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46000 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46001 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46002 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46003 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46004 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46005 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46006 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46007 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46008 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46009 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46010 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46011 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46012 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46013 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46014 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46015 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46016 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46017 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46018 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46019 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46020 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46021 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46022 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46023 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46024 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46025 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46026 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46027 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46028 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46029 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46030 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46031 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46032 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46033 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46034 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46035 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46036 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46037 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46038 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46039 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46040 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46041 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46042 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46043 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause46044 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46045 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46046 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46047 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46048 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46049 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46050 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46051 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46052 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46053 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46054 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46055 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46056 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46057 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46058 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46059 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46060 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46061 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46062 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46063 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46064 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46065 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46066 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46067 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46068 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46069 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46070 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46071 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46072 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46073 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46074 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46075 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46076 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46077 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46078 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46079 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46080 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46081 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46082 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46083 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46084 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46085 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46086 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46087 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46088 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46089 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46090 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46091 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46092 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46093 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46094 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46095 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46096 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46097 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46098 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46099 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46100 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46101 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause46102 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46103 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46104 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46105 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46106 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46107 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46108 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46109 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46110 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46111 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46112 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46113 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46114 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46115 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46116 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46117 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46118 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46119 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46120 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46121 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46122 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46123 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46124 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46125 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46126 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46127 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46128 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46129 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46130 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46131 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46132 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46133 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46134 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46135 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46136 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46137 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46138 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46139 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46140 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46141 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46142 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46143 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46144 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46145 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause46146 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46147 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46148 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46149 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46150 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46151 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46152 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46153 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46154 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46155 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46156 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46157 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46158 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause46159 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause46160 chi hallowed hno hanchor hbad

end ErdosSzekeres

end
