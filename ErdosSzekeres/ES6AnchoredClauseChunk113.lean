module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Retained anchored ES(6) semantic clauses, group 113. -/

theorem es6Anchored_clause14464 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14465 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14466 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14467 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14468 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14469 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14470 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14471 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14472 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14473 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14474 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14475 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14476 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14477 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14478 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14479 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14480 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14481 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14482 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14483 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14484 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14485 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14486 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14487 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14488 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14489 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14490 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14491 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14492 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14493 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14494 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14495 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14496 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14497 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14498 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14499 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14500 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14501 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14502 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14503 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14504 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14505 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14506 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14507 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14508 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14509 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14510 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14511 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14512 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14513 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14514 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14515 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14516 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14517 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14518 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 11 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14519 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14520 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14521 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14522 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14523 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14524 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14525 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14526 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14527 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14528 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14529 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14530 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14531 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14532 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14533 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14534 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14535 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14536 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14537 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14538 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14539 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14540 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14541 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14542 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14543 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14544 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14545 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14546 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14547 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14548 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14549 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14550 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 12 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14551 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14552 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause14553 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14554 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14555 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14556 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause14557 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause14558 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 13 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause14559 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14560 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 6] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14561 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 7] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14562 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 8] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14563 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 9] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14564 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14565 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14566 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14567 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14568 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14569 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14570 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14571 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 6] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14572 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 7] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14573 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 8] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14574 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 9] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14575 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14576 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14577 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14578 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14579 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14580 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14581 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14582 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 7] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14583 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 8] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14584 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 9] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14585 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14586 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14587 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14588 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14589 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14590 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause14591 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left) ∧
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
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

end ErdosSzekeres.ES6

end
