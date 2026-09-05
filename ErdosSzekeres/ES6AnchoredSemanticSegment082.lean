module

public import ErdosSzekeres.ES6AnchoredClauseChunk298
public import ErdosSzekeres.ES6AnchoredClauseChunk299
public import ErdosSzekeres.ES6AnchoredClauseChunk300
public import ErdosSzekeres.ES6AnchoredClauseChunk301
public import ErdosSzekeres.ES6AnchoredClauseChunk302

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Semantic rejection of balanced CNF subtree 082. -/

theorem es6Anchored_rejectSemanticSegment082
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
    ¬(((((((((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))))))) ∨
      ((((((((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      (((((((¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause38234 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38235 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38236 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38237 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38238 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38239 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38240 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38241 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38242 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38243 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38244 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38245 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38246 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38247 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38248 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38249 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38250 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38251 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38252 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38253 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38254 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38255 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38256 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38257 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38258 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38259 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38260 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38261 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38262 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38263 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38264 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38265 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38266 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38267 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38268 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38269 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38270 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38271 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38272 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38273 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38274 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38275 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38276 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38277 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38278 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38279 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38280 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38281 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38282 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38283 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38284 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38285 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38286 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38287 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38288 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38289 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38290 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38291 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38292 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38293 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38294 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38295 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38296 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38297 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38298 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38299 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38300 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38301 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38302 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38303 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38304 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38305 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38306 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38307 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38308 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38309 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38310 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38311 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38312 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38313 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38314 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38315 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38316 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38317 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38318 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38319 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38320 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38321 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38322 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38323 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38324 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38325 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38326 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38327 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38328 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38329 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38330 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38331 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38332 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38333 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38334 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38335 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38336 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38337 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38338 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38339 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38340 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38341 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38342 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38343 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38344 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38345 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38346 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38347 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38348 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38349 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38350 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38351 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38352 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38353 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38354 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38355 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38356 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38357 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38358 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38359 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38360 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38361 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38362 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38363 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38364 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38365 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38366 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38367 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38368 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38369 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38370 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38371 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38372 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38373 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38374 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38375 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38376 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38377 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38378 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38379 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38380 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38381 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38382 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38383 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38384 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38385 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38386 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38387 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38388 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38389 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38390 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38391 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38392 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38393 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38394 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38395 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38396 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38397 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38398 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38399 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38400 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38401 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38402 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38403 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38404 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38405 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38406 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38407 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38408 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38409 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38410 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38411 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38412 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38413 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38414 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38415 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38416 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38417 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38418 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38419 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38420 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38421 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38422 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38423 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38424 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38425 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38426 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38427 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38428 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38429 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38430 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38431 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38432 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38433 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38434 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38435 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38436 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38437 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38438 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38439 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38440 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38441 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38442 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38443 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38444 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38445 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38446 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38447 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38448 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38449 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38450 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38451 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38452 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38453 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38454 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38455 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38456 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38457 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38458 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38459 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38460 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38461 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38462 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38463 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38464 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38465 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38466 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38467 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38468 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38469 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38470 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38471 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38472 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38473 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38474 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38475 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38476 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38477 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38478 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38479 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38480 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38481 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38482 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38483 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38484 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38485 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38486 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38487 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38488 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38489 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38490 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38491 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38492 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38493 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38494 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38495 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38496 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38497 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38498 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38499 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38500 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38501 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38502 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38503 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38504 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38505 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38506 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38507 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38508 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38509 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38510 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38511 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38512 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38513 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38514 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38515 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38516 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38517 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38518 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38519 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38520 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38521 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38522 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38523 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38524 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38525 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38526 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38527 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38528 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38529 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38530 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38531 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38532 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38533 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38534 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38535 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38536 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38537 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38538 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38539 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38540 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38541 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38542 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38543 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38544 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38545 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38546 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38547 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38548 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38549 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38550 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38551 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38552 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38553 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38554 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38555 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38556 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38557 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38558 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38559 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38560 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38561 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38562 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38563 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38564 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38565 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38566 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38567 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38568 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38569 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38570 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38571 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38572 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38573 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38574 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38575 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38576 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38577 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38578 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38579 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38580 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38581 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38582 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38583 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38584 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38585 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38586 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38587 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38588 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38589 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38590 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38591 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38592 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38593 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38594 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38595 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38596 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38597 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38598 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38599 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38600 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38601 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38602 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38603 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38604 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38605 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38606 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38607 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38608 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38609 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38610 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38611 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38612 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38613 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38614 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38615 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38616 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38617 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38618 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38619 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38620 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38621 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38622 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38623 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38624 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38625 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38626 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38627 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38628 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38629 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38630 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38631 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38632 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38633 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38634 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38635 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38636 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38637 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38638 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38639 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38640 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause38641 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38642 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38643 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38644 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38645 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38646 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38647 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38648 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38649 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38650 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38651 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38652 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38653 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38654 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38655 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38656 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38657 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38658 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38659 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38660 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38661 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38662 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38663 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38664 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38665 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38666 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38667 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38668 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38669 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38670 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38671 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38672 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38673 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38674 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38675 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38676 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38677 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38678 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38679 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38680 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38681 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38682 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38683 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38684 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause38685 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38686 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38687 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38688 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38689 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38690 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38691 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38692 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38693 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38694 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38695 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38696 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38697 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause38698 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause38699 chi hallowed hno hanchor hbad

end ErdosSzekeres.ES6

end
