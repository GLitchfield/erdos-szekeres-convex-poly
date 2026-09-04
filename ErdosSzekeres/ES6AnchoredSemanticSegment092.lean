module

public import ErdosSzekeres.ES6AnchoredClauseChunk335
public import ErdosSzekeres.ES6AnchoredClauseChunk336
public import ErdosSzekeres.ES6AnchoredClauseChunk337
public import ErdosSzekeres.ES6AnchoredClauseChunk338

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 092. -/

theorem es6Anchored_rejectSemanticSegment092
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
    ¬(((((((((((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      (((((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))))))))) ∨
      ((((((((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))))))) ∨
      ((((((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))))) ∨
      ((((¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left))))))) ∨
      ((((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))))))) ∨
      ((((((¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left))))) ∨
      ((((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))))) ∨
      (((((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))))) ∨
      (((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))) ∨
      (((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)))))) ∨
      (((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      ((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      (¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))))) ∨
      ((((¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))) ∨
      ((((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left))) ∨
      (((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) ∨
      ((chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)))))))))))) := by
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
                  exact es6Anchored_clause42897 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42898 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42899 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42900 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42901 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42902 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42903 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42904 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42905 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42906 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42907 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42908 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42909 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42910 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42911 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42912 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42913 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42914 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42915 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42916 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42917 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42918 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42919 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42920 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42921 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42922 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42923 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42924 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42925 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42926 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42927 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42928 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42929 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42930 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42931 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42932 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42933 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42934 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42935 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42936 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42937 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42938 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42939 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42940 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42941 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42942 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42943 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42944 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42945 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42946 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42947 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42948 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42949 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42950 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42951 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42952 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42953 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42954 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause42955 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42956 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42957 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42958 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42959 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42960 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42961 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42962 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42963 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42964 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42965 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42966 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42967 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42968 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42969 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42970 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42971 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42972 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42973 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42974 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42975 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42976 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42977 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42978 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42979 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42980 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42981 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42982 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42983 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42984 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42985 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42986 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42987 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42988 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42989 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42990 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42991 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42992 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42993 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42994 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42995 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42996 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause42997 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause42998 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause42999 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43000 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43001 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43002 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43003 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43004 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43005 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43006 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43007 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43008 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43009 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43010 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43011 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43012 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause43013 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43014 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43015 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43016 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43017 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43018 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43019 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43020 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43021 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43022 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43023 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43024 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43025 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43026 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43027 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43028 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43029 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43030 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43031 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43032 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43033 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43034 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43035 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43036 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43037 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43038 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43039 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43040 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43041 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43042 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43043 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43044 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43045 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43046 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43047 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43048 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43049 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43050 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43051 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43052 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43053 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43054 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43055 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43056 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43057 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43058 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43059 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43060 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43061 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43062 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43063 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43064 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43065 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43066 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43067 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43068 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43069 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43070 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause43071 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43072 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43073 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43074 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43075 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43076 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43077 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43078 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43079 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43080 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43081 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43082 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43083 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43084 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43085 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43086 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43087 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43088 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43089 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43090 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43091 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43092 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43093 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43094 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43095 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43096 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43097 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43098 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43099 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43100 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43101 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43102 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43103 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43104 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43105 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43106 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43107 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43108 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43109 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43110 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43111 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43112 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43113 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43114 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43115 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43116 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43117 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43118 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43119 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43120 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43121 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43122 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43123 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43124 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43125 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43126 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43127 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43128 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43129 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause43130 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43131 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43132 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43133 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43134 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43135 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43136 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43137 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43138 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43139 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43140 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43141 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43142 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43143 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43144 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43145 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43146 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43147 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43148 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43149 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43150 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43151 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43152 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43153 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43154 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43155 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43156 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43157 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43158 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43159 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43160 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43161 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43162 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43163 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43164 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43165 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43166 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43167 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43168 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43169 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43170 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43171 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43172 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43173 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43174 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43175 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43176 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43177 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43178 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43179 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43180 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43181 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43182 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43183 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43184 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43185 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43186 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43187 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause43188 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43189 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43190 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43191 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43192 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43193 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43194 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43195 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43196 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43197 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43198 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43199 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43200 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43201 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43202 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43203 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43204 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43205 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43206 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43207 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43208 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43209 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43210 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43211 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43212 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43213 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43214 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43215 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43216 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43217 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43218 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43219 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43220 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43221 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43222 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43223 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43224 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43225 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43226 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43227 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43228 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43229 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43230 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43231 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43232 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43233 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43234 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43235 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43236 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43237 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43238 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43239 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43240 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43241 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43242 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43243 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43244 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43245 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause43246 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43247 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43248 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43249 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43250 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43251 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43252 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43253 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43254 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43255 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43256 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43257 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43258 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43259 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43260 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43261 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43262 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43263 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43264 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43265 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43266 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43267 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43268 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43269 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43270 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43271 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43272 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43273 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43274 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43275 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43276 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43277 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43278 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43279 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43280 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43281 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43282 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43283 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43284 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43285 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43286 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43287 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43288 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43289 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43290 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43291 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43292 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43293 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43294 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43295 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43296 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43297 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43298 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43299 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43300 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43301 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43302 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43303 chi hallowed hno hanchor hbad
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
                  exact es6Anchored_clause43304 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43305 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43306 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43307 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43308 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43309 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43310 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43311 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43312 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43313 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43314 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43315 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43316 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43317 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43318 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43319 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43320 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43321 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43322 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43323 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43324 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43325 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43326 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43327 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43328 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43329 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43330 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43331 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43332 chi hallowed hno hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43333 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43334 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43335 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43336 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43337 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43338 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43339 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43340 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43341 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43342 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43343 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43344 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43345 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43346 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43347 chi hallowed hno hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact es6Anchored_clause43348 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43349 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43350 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43351 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43352 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43353 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43354 chi hallowed hno hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43355 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43356 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43357 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43358 chi hallowed hno hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43359 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43360 chi hallowed hno hanchor hbad
                ·
                  rcases hbad with hbad | hbad
                  ·
                    exact es6Anchored_clause43361 chi hallowed hno hanchor hbad
                  ·
                    exact es6Anchored_clause43362 chi hallowed hno hanchor hbad

end ErdosSzekeres

end
