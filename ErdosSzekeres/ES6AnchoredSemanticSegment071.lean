module

public import ErdosSzekeres.ES6AnchoredClauseChunk258
public import ErdosSzekeres.ES6AnchoredClauseChunk259
public import ErdosSzekeres.ES6AnchoredClauseChunk260
public import ErdosSzekeres.ES6AnchoredClauseChunk261
public import ErdosSzekeres.ES6AnchoredClauseChunk262

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 071. -/

theorem es6Anchored_rejectSemanticSegment071
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
    ¬(((((((((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))))))))) ∨
      ((((((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
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
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause33105 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33106 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33107 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33108 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33109 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33110 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33111 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33112 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33113 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33114 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33115 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33116 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33117 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33118 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33119 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33120 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33121 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33122 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33123 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33124 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33125 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33126 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33127 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33128 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33129 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33130 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33131 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33132 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33133 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33134 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33135 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33136 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33137 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33138 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33139 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33140 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33141 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33142 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33143 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33144 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33145 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33146 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33147 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33148 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33149 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33150 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33151 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33152 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33153 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33154 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33155 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33156 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33157 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33158 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33159 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33160 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33161 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33162 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33163 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33164 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33165 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33166 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33167 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33168 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33169 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33170 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33171 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33172 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33173 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33174 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33175 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33176 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33177 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33178 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33179 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33180 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33181 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33182 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33183 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33184 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33185 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33186 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33187 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33188 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33189 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33190 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33191 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33192 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33193 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33194 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33195 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33196 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33197 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33198 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33199 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33200 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33201 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33202 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33203 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33204 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33205 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33206 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33207 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33208 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33209 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33210 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33211 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33212 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33213 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33214 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33215 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33216 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33217 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33218 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33219 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33220 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33221 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33222 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33223 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33224 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33225 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33226 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33227 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33228 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33229 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33230 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33231 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33232 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33233 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33234 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33235 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33236 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33237 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33238 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33239 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33240 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33241 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33242 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33243 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33244 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33245 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33246 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33247 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33248 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33249 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33250 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33251 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33252 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33253 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33254 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33255 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33256 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33257 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33258 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33259 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33260 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33261 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33262 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33263 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33264 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33265 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33266 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33267 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33268 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33269 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33270 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33271 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33272 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33273 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33274 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33275 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33276 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33277 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33278 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33279 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33280 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33281 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33282 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33283 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33284 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33285 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33286 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33287 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33288 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33289 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33290 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33291 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33292 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33293 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33294 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33295 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33296 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33297 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33298 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33299 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33300 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33301 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33302 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33303 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33304 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33305 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33306 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33307 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33308 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33309 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33310 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33311 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33312 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33313 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33314 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33315 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33316 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33317 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33318 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33319 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33320 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33321 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33322 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33323 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33324 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33325 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33326 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33327 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33328 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33329 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33330 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33331 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33332 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33333 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33334 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33335 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33336 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33337 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33338 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33339 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33340 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33341 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33342 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33343 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33344 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33345 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33346 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33347 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33348 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33349 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33350 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33351 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33352 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33353 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33354 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33355 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33356 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33357 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33358 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33359 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33360 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33361 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33362 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33363 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33364 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33365 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33366 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33367 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33368 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33369 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33370 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33371 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33372 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33373 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33374 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33375 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33376 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33377 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33378 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33379 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33380 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33381 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33382 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33383 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33384 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33385 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33386 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33387 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33388 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33389 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33390 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33391 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33392 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33393 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33394 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33395 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33396 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33397 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33398 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33399 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33400 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33401 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33402 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33403 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33404 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33405 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33406 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33407 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33408 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33409 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33410 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33411 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33412 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33413 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33414 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33415 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33416 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33417 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33418 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33419 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33420 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33421 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33422 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33423 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33424 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33425 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33426 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33427 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33428 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33429 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33430 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33431 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33432 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33433 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33434 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33435 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33436 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33437 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33438 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33439 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33440 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33441 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33442 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33443 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33444 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33445 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33446 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33447 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33448 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33449 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33450 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33451 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33452 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33453 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33454 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33455 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33456 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33457 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33458 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33459 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33460 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33461 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33462 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33463 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33464 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33465 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33466 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33467 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33468 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33469 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33470 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33471 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33472 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33473 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33474 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33475 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33476 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33477 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33478 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33479 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33480 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33481 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33482 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33483 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33484 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33485 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33486 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33487 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33488 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33489 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33490 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33491 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33492 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33493 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33494 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33495 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33496 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33497 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33498 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33499 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33500 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33501 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33502 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33503 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33504 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33505 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33506 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33507 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33508 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33509 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33510 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33511 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33512 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause33513 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33514 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33515 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33516 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33517 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33518 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33519 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33520 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33521 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33522 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33523 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33524 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33525 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33526 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33527 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33528 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33529 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33530 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33531 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33532 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33533 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33534 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33535 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33536 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33537 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33538 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33539 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33540 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33541 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33542 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33543 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33544 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33545 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33546 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33547 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33548 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33549 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33550 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33551 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33552 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33553 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33554 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33555 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33556 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause33557 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33558 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33559 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33560 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33561 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33562 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33563 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33564 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33565 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33566 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33567 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33568 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33569 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause33570 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause33571 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
