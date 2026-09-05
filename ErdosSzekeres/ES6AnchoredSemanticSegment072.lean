module

public import ErdosSzekeres.ES6AnchoredClauseChunk262
public import ErdosSzekeres.ES6AnchoredClauseChunk263
public import ErdosSzekeres.ES6AnchoredClauseChunk264
public import ErdosSzekeres.ES6AnchoredClauseChunk265

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 072. -/

theorem es6Anchored_rejectSemanticSegment072
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
    ¬(((((((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
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
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
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
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
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
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
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
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      (((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      (((¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))))))) ∨
      (((((((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
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
      (¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
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
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
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
      ((((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause33572 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33573 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33574 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33575 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33576 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33577 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33578 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33579 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33580 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33581 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33582 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33583 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33584 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33585 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33586 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33587 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33588 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33589 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33590 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33591 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33592 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33593 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33594 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33595 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33596 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33597 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33598 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33599 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33600 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33601 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33602 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33603 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33604 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33605 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33606 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33607 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33608 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33609 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33610 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33611 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33612 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33613 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33614 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33615 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33616 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33617 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33618 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33619 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33620 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33621 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33622 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33623 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33624 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33625 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33626 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33627 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33628 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33629 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33630 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33631 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33632 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33633 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33634 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33635 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33636 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33637 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33638 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33639 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33640 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33641 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33642 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33643 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33644 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33645 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33646 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33647 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33648 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33649 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33650 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33651 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33652 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33653 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33654 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33655 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33656 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33657 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33658 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33659 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33660 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33661 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33662 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33663 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33664 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33665 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33666 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33667 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33668 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33669 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33670 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33671 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33672 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33673 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33674 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33675 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33676 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33677 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33678 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33679 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33680 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33681 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33682 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33683 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33684 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33685 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33686 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33687 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33688 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33689 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33690 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33691 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33692 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33693 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33694 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33695 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33696 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33697 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33698 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33699 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33700 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33701 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33702 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33703 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33704 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33705 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33706 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33707 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33708 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33709 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33710 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33711 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33712 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33713 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33714 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33715 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33716 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33717 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33718 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33719 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33720 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33721 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33722 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33723 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33724 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33725 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33726 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33727 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33728 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33729 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33730 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33731 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33732 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33733 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33734 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33735 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33736 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33737 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33738 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33739 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33740 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33741 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33742 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33743 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33744 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33745 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33746 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33747 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33748 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33749 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33750 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33751 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33752 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33753 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33754 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33755 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33756 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33757 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33758 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33759 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33760 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33761 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33762 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33763 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33764 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33765 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33766 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33767 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33768 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33769 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33770 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33771 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33772 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33773 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33774 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33775 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33776 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33777 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33778 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33779 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33780 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33781 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33782 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33783 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33784 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33785 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33786 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33787 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33788 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33789 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33790 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33791 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33792 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33793 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33794 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33795 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33796 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33797 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33798 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33799 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33800 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33801 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33802 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33803 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33804 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33805 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33806 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33807 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33808 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33809 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33810 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33811 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33812 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33813 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33814 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33815 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33816 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33817 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33818 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33819 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33820 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33821 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33822 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33823 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33824 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33825 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33826 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33827 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33828 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33829 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33830 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33831 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33832 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33833 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33834 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33835 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33836 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33837 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33838 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33839 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33840 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33841 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33842 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33843 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33844 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33845 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33846 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33847 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33848 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33849 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33850 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33851 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33852 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33853 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33854 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33855 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33856 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33857 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33858 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33859 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33860 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33861 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33862 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33863 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33864 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33865 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33866 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33867 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33868 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33869 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33870 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33871 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33872 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33873 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33874 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33875 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33876 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33877 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33878 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33879 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33880 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33881 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33882 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33883 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33884 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33885 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33886 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33887 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33888 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33889 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33890 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33891 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33892 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33893 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33894 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33895 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33896 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33897 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33898 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33899 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33900 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33901 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33902 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33903 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33904 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33905 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33906 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33907 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33908 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33909 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33910 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33911 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33912 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33913 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33914 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33915 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33916 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33917 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33918 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33919 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33920 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33921 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33922 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33923 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33924 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33925 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33926 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33927 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33928 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33929 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33930 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33931 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33932 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33933 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33934 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33935 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33936 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33937 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33938 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33939 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33940 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33941 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33942 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33943 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33944 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33945 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33946 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33947 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33948 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33949 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33950 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33951 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33952 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33953 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33954 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33955 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33956 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33957 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33958 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33959 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33960 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33961 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33962 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33963 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33964 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33965 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33966 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33967 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33968 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33969 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33970 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33971 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33972 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33973 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33974 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33975 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33976 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33977 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33978 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33979 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33980 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33981 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33982 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33983 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33984 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33985 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33986 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33987 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33988 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33989 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33990 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33991 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33992 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33993 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33994 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33995 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33996 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33997 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33998 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33999 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34000 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34001 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34002 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34003 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34004 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34005 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34006 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34007 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause34008 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34009 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34010 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34011 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34012 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34013 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34014 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34015 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34016 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34017 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34018 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34019 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34020 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34021 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34022 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause34023 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34024 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34025 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34026 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34027 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34028 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34029 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34030 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34031 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34032 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34033 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34034 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34035 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause34036 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause34037 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
