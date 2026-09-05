module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Retained anchored ES(6) semantic clauses, group 082. -/

theorem es6Anchored_clause10496 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10497 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10498 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10499 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10500 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10501 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10502 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10503 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10504 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10505 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10506 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10507 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10508 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10509 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10510 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10511 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10512 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10513 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10514 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10515 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10516 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10517 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10518 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 11 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10519 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10520 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10521 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10522 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10523 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10524 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10525 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10526 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10527 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10528 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10529 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10530 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10531 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10532 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10533 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10534 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10535 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10536 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10537 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10538 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10539 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10540 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10541 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10542 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10543 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10544 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10545 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10546 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10547 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10548 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10549 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10550 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10551 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10552 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10553 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10554 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10555 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10556 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10557 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10558 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10559 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10560 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10561 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10562 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10563 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10564 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10565 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10566 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 12 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10567 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10568 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10569 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10570 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10571 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10572 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10573 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10574 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10575 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10576 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10577 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10578 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10579 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10580 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10581 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10582 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10583 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10584 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10585 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10586 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10587 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10588 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10589 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10590 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 13 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10591 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10592 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10593 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10594 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10595 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10596 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10597 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10598 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 4 14 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10599 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10600 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10601 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10602 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10603 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10604 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10605 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10606 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10607 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10608 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10609 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10610 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10611 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10612 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10613 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10614 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10615 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10616 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause10617 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10618 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10619 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10620 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause10621 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause10622 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause10623 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 5 6 7 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

end ErdosSzekeres.ES6

end
